#!/usr/bin/env python3
"""A1 round-trip prototype: deployed Python  <->  the Lean `Imp` embedding.

Mechanises the hand-transcription that `Wikifunctions/Python/*Prog.lean` currently
does by eye. Three directions:

  * translate : Python source  -> `Imp` AST      (via the std-lib `ast` module)
  * render_py : `Imp` AST       -> Python source
  * lean_*    : `Imp` AST       -> Lean `Stmt`/program terms + a kernel check

The point is to shrink per-function trust to per-*construct* trust: every Python
node handled below maps to exactly one `Imp` constructor (see README for the
table). The single non-1:1 rule is the documented `for ... range` -> `while`
desugaring. Anything outside the handled fragment raises `Unsupported` — the tool
never guesses.

Scope: the fragment used by the two deployed programs (Z29182 coprime, Z13668
factorial). This is a prototype, not a general Python front end.
"""
from __future__ import annotations

import ast
import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent


class Unsupported(Exception):
    """A Python construct outside the handled fragment. Never silently guessed."""


# ---------------------------------------------------------------------------
# The Imp AST, mirroring Wikifunctions/Python/Imp.lean one-for-one.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Var:  # Expr.var
    x: str
@dataclass(frozen=True)
class Lit:  # Expr.lit
    n: int
@dataclass(frozen=True)
class Add:  # Expr.add
    a: object; b: object
@dataclass(frozen=True)
class Mul:  # Expr.mul
    a: object; b: object
@dataclass(frozen=True)
class Mod:  # Expr.mod
    a: object; b: object

@dataclass(frozen=True)
class Ne0:  # Cond.ne0   ( e != 0 )
    e: object
@dataclass(frozen=True)
class Le:   # Cond.le    ( a <= b )
    a: object; b: object

@dataclass(frozen=True)
class Passign:  # Stmt.passign   ( x1, x2 = e1, e2 )
    x1: str; x2: str; e1: object; e2: object
@dataclass(frozen=True)
class While:    # Stmt.while_
    c: object; body: object
@dataclass(frozen=True)
class Seq:      # Stmt.seq
    a: object; b: object


@dataclass
class Program:
    name: str
    params: list[str]
    # ordered initial store: (var, ('param', name) | ('lit', n))
    init: list[tuple[str, tuple]]
    body: object          # the loop Stmt
    result: tuple         # ('bool_eq', var, const) | ('nat', var)
    fuel_var: str         # the variable that bounds the loop (fuel = its value + 1)


# ---------------------------------------------------------------------------
# Python  ->  Imp
# ---------------------------------------------------------------------------
def tr_expr(e: ast.expr) -> object:
    if isinstance(e, ast.Name):
        return Var(e.id)
    if isinstance(e, ast.Constant) and isinstance(e.value, int) and not isinstance(e.value, bool):
        return Lit(e.value)
    if isinstance(e, ast.BinOp):
        a, b = tr_expr(e.left), tr_expr(e.right)
        if isinstance(e.op, ast.Add):  return Add(a, b)
        if isinstance(e.op, ast.Mult): return Mul(a, b)
        if isinstance(e.op, ast.Mod):  return Mod(a, b)
        raise Unsupported(f"binary operator {ast.dump(e.op)}")
    raise Unsupported(f"expression {ast.dump(e)}")


def tr_cond(t: ast.expr) -> object:
    if isinstance(t, ast.Compare) and len(t.ops) == 1:
        op, right = t.ops[0], t.comparators[0]
        if isinstance(op, ast.NotEq) and isinstance(right, ast.Constant) and right.value == 0:
            return Ne0(tr_expr(t.left))               # x != 0
        if isinstance(op, ast.LtE):
            return Le(tr_expr(t.left), tr_expr(right))  # a <= b
    raise Unsupported(f"condition {ast.dump(t)} (only `x != 0` and `a <= b`)")


def tr_passign(s: ast.stmt) -> Passign:
    """`x1, x2 = e1, e2` — a *binary* parallel assignment (Imp has no other arity)."""
    if (isinstance(s, ast.Assign) and len(s.targets) == 1
            and isinstance(s.targets[0], ast.Tuple) and isinstance(s.value, ast.Tuple)
            and len(s.targets[0].elts) == 2 and len(s.value.elts) == 2
            and all(isinstance(t, ast.Name) for t in s.targets[0].elts)):
        (x1, x2) = (t.id for t in s.targets[0].elts)
        e1, e2 = (tr_expr(v) for v in s.value.elts)
        return Passign(x1, x2, e1, e2)
    raise Unsupported(f"loop body must be `x1, x2 = e1, e2`, got {ast.dump(s)}")


def tr_block(stmts: list[ast.stmt]) -> object:
    body = [tr_passign(s) for s in stmts]
    out = body[-1]
    for s in reversed(body[:-1]):
        out = Seq(s, out)
    return out


def _upper_bound(hi: ast.expr) -> object:
    """range(lo, hi) iterates while ctr <= hi-1. Imp has no subtraction, so we
    only accept the two forms that yield a subtraction-free bound."""
    if isinstance(hi, ast.BinOp) and isinstance(hi.op, ast.Add) \
            and isinstance(hi.right, ast.Constant) and hi.right.value == 1:
        return tr_expr(hi.left)                 # (n + 1) - 1  ==  n
    if isinstance(hi, ast.Constant) and isinstance(hi.value, int):
        return Lit(hi.value - 1)                # literal c    ->  c-1
    raise Unsupported("range upper bound must be `<expr> + 1` or an int literal")


def _fuse_for(node: ast.For) -> tuple[str, object, int, object]:
    """Desugar `for ctr in range(lo, hi): acc <op>= e` into a while loop whose
    body fuses the accumulator update with the counter increment. Returns
    (ctr, upper_bound_expr, lo, accumulator_update_expr)."""
    if not (isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name)
            and node.iter.func.id == "range" and len(node.iter.args) == 2):
        raise Unsupported("only `for i in range(lo, hi)` is handled")
    if not isinstance(node.target, ast.Name):
        raise Unsupported("range loop target must be a plain variable")
    lo = node.iter.args[0]
    if not (isinstance(lo, ast.Constant) and isinstance(lo.value, int)):
        raise Unsupported("range lower bound must be an int literal")
    bound = _upper_bound(node.iter.args[1])
    if len(node.body) != 1:
        raise Unsupported("range loop body must be a single accumulator update")
    s = node.body[0]
    if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name):
        acc = s.target.id
        rhs = tr_expr(s.value)
        if isinstance(s.op, ast.Mult):  upd = Mul(Var(acc), rhs)
        elif isinstance(s.op, ast.Add): upd = Add(Var(acc), rhs)
        else: raise Unsupported(f"augmented op {ast.dump(s.op)}")
    elif isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
        acc = s.targets[0].id
        upd = tr_expr(s.value)
    else:
        raise Unsupported(f"range loop body {ast.dump(s)}")
    return node.target.id, bound, lo.value, (acc, upd)


def translate(src: str) -> Program:
    tree = ast.parse(src)
    if len(tree.body) != 1 or not isinstance(tree.body[0], ast.FunctionDef):
        raise Unsupported("expected a single top-level function definition")
    fn = tree.body[0]
    params = [a.arg for a in fn.args.args]
    init: list[tuple[str, tuple]] = [(p, ("param", p)) for p in params]
    body = result = fuel_var = None

    for node in fn.body:
        # pre-loop constant assignment  x = c   ->  folded into the initial store
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Constant) and isinstance(node.value.value, int)):
            init.append((node.targets[0].id, ("lit", node.value.value)))
        elif isinstance(node, ast.While):
            cond = tr_cond(node.test)
            body = While(cond, tr_block(node.body))
            fuel_var = cond.e.x if isinstance(cond, Ne0) else cond.b.x  # loop-bounding var
        elif isinstance(node, ast.For):
            ctr, bound, lo, (acc, upd) = _fuse_for(node)
            init.append((ctr, ("lit", lo)))
            body = While(Le(Var(ctr), bound), Passign(acc, ctr, upd, Add(Var(ctr), Lit(1))))
            fuel_var = bound.x if isinstance(bound, Var) else ctr
        elif isinstance(node, ast.Return):
            v = node.value
            if (isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq)
                    and isinstance(v.left, ast.Name) and isinstance(v.comparators[0], ast.Constant)):
                result = ("bool_eq", v.left.id, v.comparators[0].value)
            elif isinstance(v, ast.Name):
                result = ("nat", v.id)
            else:
                raise Unsupported(f"return {ast.dump(v)} (only `x == c` or `x`)")
        else:
            raise Unsupported(f"top-level statement {ast.dump(node)}")

    if body is None or result is None:
        raise Unsupported("program must contain one loop and a return")
    return Program(fn.name, params, init, body, result, fuel_var)


# ---------------------------------------------------------------------------
# Imp  ->  Python  (prints the while-form; for a genuine while loop this is exact)
# ---------------------------------------------------------------------------
def render_expr(e) -> str:
    if isinstance(e, Var): return e.x
    if isinstance(e, Lit): return str(e.n)
    if isinstance(e, Add): return f"{render_expr(e.a)} + {render_expr(e.b)}"
    if isinstance(e, Mul): return f"{render_expr(e.a)} * {render_expr(e.b)}"
    if isinstance(e, Mod): return f"{render_expr(e.a)} % {render_expr(e.b)}"
    raise Unsupported(str(e))


def render_cond(c) -> str:
    if isinstance(c, Ne0): return f"{render_expr(c.e)} != 0"
    if isinstance(c, Le):  return f"{render_expr(c.a)} <= {render_expr(c.b)}"
    raise Unsupported(str(c))


def render_stmt(s, ind: int) -> str:
    pad = "    " * ind
    if isinstance(s, Passign):
        return f"{pad}{s.x1}, {s.x2} = {render_expr(s.e1)}, {render_expr(s.e2)}"
    if isinstance(s, While):
        return f"{pad}while {render_cond(s.c)}:\n{render_stmt(s.body, ind + 1)}"
    if isinstance(s, Seq):
        return f"{render_stmt(s.a, ind)}\n{render_stmt(s.b, ind)}"
    raise Unsupported(str(s))


def render_py(p: Program) -> str:
    lines = [f"def {p.name}({', '.join(p.params)}):"]
    for var, val in p.init:
        if val[0] == "lit":                       # params are function args, not lines
            lines.append(f"    {var} = {val[1]}")
    lines.append(render_stmt(p.body, 1))
    if p.result[0] == "bool_eq":
        lines.append(f"    return {p.result[1]} == {p.result[2]}")
    else:
        lines.append(f"    return {p.result[1]}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Imp  ->  Lean terms + a kernel-checked equality against the committed defs
# ---------------------------------------------------------------------------
def lean_expr(e) -> str:
    if isinstance(e, Var): return f'(.var "{e.x}")'
    if isinstance(e, Lit): return f"(.lit {e.n})"
    if isinstance(e, Add): return f"(.add {lean_expr(e.a)} {lean_expr(e.b)})"
    if isinstance(e, Mul): return f"(.mul {lean_expr(e.a)} {lean_expr(e.b)})"
    if isinstance(e, Mod): return f"(.mod {lean_expr(e.a)} {lean_expr(e.b)})"
    raise Unsupported(str(e))


def lean_cond(c) -> str:
    if isinstance(c, Ne0): return f"(.ne0 {lean_expr(c.e)})"
    if isinstance(c, Le):  return f"(.le {lean_expr(c.a)} {lean_expr(c.b)})"
    raise Unsupported(str(c))


def lean_stmt(s) -> str:
    if isinstance(s, Passign):
        return f'(.passign "{s.x1}" "{s.x2}" {lean_expr(s.e1)} {lean_expr(s.e2)})'
    if isinstance(s, While):
        return f"(.while_ {lean_cond(s.c)} {lean_stmt(s.body)})"
    if isinstance(s, Seq):
        return f"(.seq {lean_stmt(s.a)} {lean_stmt(s.b)})"
    raise Unsupported(str(s))


def lean_init(p: Program, binders: list[str]) -> str:
    """The initial store as a term over the parameter binders (positional)."""
    pm = {name: binders[i] for i, name in enumerate(p.params)}
    term = "([] : State)"
    for var, val in p.init:
        v = pm[val[1]] if val[0] == "param" else str(val[1])
        term = f'(State.set {term} "{var}" {v})'
    return term


# Which committed defs each program should be checked against.
COMMITTED = {
    "Z13701": dict(module="Wikifunctions.Python.Z13701Prog",
                   loop="loop", init="initState", run="runProgram"),
    "Z13667": dict(module="Wikifunctions.Python.Z13667Prog",
                   loop="facLoop", init="facInit", run="runFac"),
}


def lean_check(p: Program) -> str:
    c = COMMITTED[p.name]
    binders = [chr(ord("a") + i) for i in range(len(p.params))]  # a, b, ...
    bind = " ".join(binders)
    fuel_binder = binders[p.params.index(p.fuel_var)]
    init_call = f"{c['init']} {bind}"
    if p.result[0] == "bool_eq":
        ret = f'some (State.get t "{p.result[1]}" == {p.result[2]})'
    else:
        ret = f'some (State.get t "{p.result[1]}")'
    shell = (f"(match {c['loop']}.run ({fuel_binder} + 1) ({init_call}) with\n"
             f"     | none => none\n     | some t => {ret})")
    return f"""import {c['module']}

/-! AUTO-GENERATED by roundtrip/py2imp.py from roundtrip/programs/{p.name}.py.

If this file elaborates with no errors, the Lean kernel has certified that the
mechanically-translated Imp program is DEFINITIONALLY EQUAL to the committed
hand-transcription in {c['module'].split('.')[-1]}.lean — i.e. the transcription
introduces nothing the translator does not, retiring the D9 transcription-trust
gap for this program. -/

open Wikifunctions.Python
set_option linter.unusedVariables false  -- `rfl` does not reference the ∀-binders

-- the loop (control flow + parallel assignment)
example : {c['loop']} = {lean_stmt(p.body)} := rfl

-- the initial store
example : ∀ {bind}, {c['init']} {bind} = {lean_init(p, binders)} := fun {bind} => rfl

-- the whole program (fuel bound + return shell)
example : ∀ {bind}, {c['run']} {bind} =
    {shell} := fun {bind} => rfl
"""


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _load(path: str) -> Program:
    return translate(Path(path).read_text())


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("usage: py2imp.py {translate|render|check} <program.py>", file=sys.stderr)
        return 2
    cmd, path = argv[0], argv[1]
    p = _load(path)
    if cmd == "translate":
        print(f"-- {p.name}: loop\n{lean_stmt(p.body)}")
    elif cmd == "render":
        print(render_py(p), end="")
    elif cmd == "check":
        out = HERE / "generated" / f"{p.name}Check.lean"
        out.write_text(lean_check(p))
        print(f"wrote {out}")
    else:
        print(f"unknown command {cmd}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
