# A1 — Python ↔ `Imp` round-trip (prototype)

Mechanises the step that `Wikifunctions/Python/*Prog.lean` currently does **by
eye**: transcribing a deployed Wikifunctions Python implementation into the Lean
`Imp` embedding. Doing it by hand is a per-*function* act of trust (the D9 finding
in [`SPEC_AUDIT.md`](../SPEC_AUDIT.md)). This tool replaces it with a per-*construct*
mapping — small, fixed, and auditable once — and then lets the **Lean kernel**
certify that the committed transcription is exactly what the mapping produces.

```
python source ──translate──▶ Imp AST ──render_py──▶ python source
                               │
                               └──lean_stmt / lean_check──▶ Lean term + `rfl` certificate
```

## Why this shrinks the trust

A hand-transcription asks you to believe, per function, "this `Imp` term faithfully
copies that Python." The translator reduces the question to "does each of the ~14
construct rules below match?" — checked once, for all functions in the fragment.
Everything the translator emits for the two deployed programs is then proven, by
`rfl`, definitionally equal to the committed `Prog.lean` (see [Kernel certificate](#kernel-certificate)).

## The per-construct mapping (the whole trusted base)

| Python | `Imp` | 1:1? |
|---|---|---|
| `Name x` | `.var "x"` | ✓ |
| int literal `n` | `.lit n` | ✓ |
| `a + b` / `a * b` / `a % b` | `.add` / `.mul` / `.mod` | ✓ |
| `x != 0` | `.ne0` | ✓ (only `!= 0`) |
| `a <= b` | `.le` | ✓ |
| `x1, x2 = e1, e2` | `.passign x1 x2 e1 e2` | ✓ (arity exactly 2) |
| `while C: B` | `.while_ C B` | ✓ |
| statement sequence | `.seq` | ✓ |
| `x = c` before the loop (int const) | fold into the initial store | fold-in |
| `for i in range(lo, hi): acc <op>= e` | `i := lo` + `.while_ (.le i hi⁻¹) (.passign acc i <upd> (.add i 1))` | **desugaring** |
| `return x == c` | boolean result `State.get t "x" == c` | wrapper |
| `return x` | nat result `State.get t "x"` | wrapper |

Twelve of the fourteen rules are 1:1 leaf/structural maps. **One** is a fold-in
(pre-loop constant assignments become the initial `State`). **One** is a genuine
desugaring: a `for … range` loop becomes a `while` whose body fuses the accumulator
update with the counter increment into a single parallel assignment — this is the
only place `render_py ∘ translate` is not the identity on Python source, and it is
exactly the caveat already documented in `Z13667Prog.lean`. Anything outside this
table raises `Unsupported`; the translator never guesses.

## Round-trip properties (`test_roundtrip.py`)

- **P1 — Imp idempotence.** `translate(render(translate(src))) == translate(src)`.
  The `Imp` fixed point is stable even across the desugaring, so it holds for
  **both** programs.
- **P2 — Python fidelity.** `ast(render(translate(src))) == ast(src)`. Byte-for-byte
  (AST-equal) reconstruction — holds for the genuine while-loop `Z13701`; for the
  desugared `for` loop `Z13667` it is *expected* to differ (while-form vs for-form)
  and is asserted as such.
- **P3 — Kernel certificate.** `lake env lean` accepts `generated/*Check.lean`.

## Kernel certificate

`py2imp.py check <prog>` emits `generated/<Z>Check.lean`, e.g.:

```lean
example : loop = (.while_ (.ne0 (.var "Z13701K2")) (.passign …)) := rfl
example : ∀ a b, initState a b = (State.set (State.set ([] : State) "Z13701K1" a) "Z13701K2" b) := fun a b => rfl
example : ∀ a b, runProgram a b = (match loop.run (b + 1) (initState a b) with …) := fun a b => rfl
```

If it elaborates, the kernel has certified that the committed hand-transcription is
**definitionally equal** to the mechanical translation — retiring the D9
transcription-trust gap for that program. Both programs pass today.

## Run it

```bash
python3 roundtrip/py2imp.py translate roundtrip/programs/Z13701.py   # the Imp loop term
python3 roundtrip/py2imp.py render   roundtrip/programs/Z13667.py    # Imp -> Python (while-form)
python3 roundtrip/py2imp.py check    roundtrip/programs/Z13701.py    # emit generated/Z13701Check.lean
python3 roundtrip/test_roundtrip.py                                  # P1+P2+P3 for both programs
```

`test_roundtrip.py` needs a built Lean project (`lake exe cache get && lake build`)
for the P3 step; P1/P2 are pure Python.

## Scope and honest limits

- **A prototype for the deployed fragment**, not a Python front end. It handles
  exactly the constructs of `Z29182` (coprime) and `Z13668` (factorial). New
  functions grow the table one construct at a time — the burden scales with the
  functions verified, not with Python.
- `Imp`'s `passign` is **binary**, so a `for` body with more than one accumulator
  is `Unsupported`; `range` must have step 1 and a lower bound that is an int
  literal (its counter init is a `State` binding), and an upper bound of the form
  `<expr> + 1` or an int literal (`Imp` has no subtraction).
- The **fuel** expression (`bound + 1`) is emitted heuristically; that it is
  *sufficient* is a separate theorem proved in `Z13701.lean` / `Z13667.lean`
  (`loop_correct` / `facLoop_correct`), not by the translator.
- This closes the *transcription* gap, not the *semantics* gap: whether `Imp`
  itself faithfully models the deployed RustPython/wasm interpreter on this subset
  remains the trust assumption in `Imp.lean` (findings D5, D11, D12), discharged
  empirically by `native/`.

## Next

- Fetch the deployed source straight from the live API (`wikilambda_fetch` →
  `Z14K3` code) instead of the vendored `programs/*.py`, so the round-trip is
  against production on every run.
- Grow the construct table as more Python-coded functions enter the corpus.
- A parallel `Imp → JavaScript` printer would give the same round-trip for the
  JS implementations.
