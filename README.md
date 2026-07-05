# Wikifunctions × Lean

A machine-checked **Lean 4 model of the [Wikifunctions](https://www.wikifunctions.org) /
WikiLambda object system**, built ground-up from the spec. One organising principle, taken
straight from the [Function model](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z1/ZObjects):

> **Every value is a `Z1`/ZObject** — a list of key/value pairs, bottoming out in the two
> terminal types `Z6`/String and `Z9`/Reference.

So the model is a single inductive type plus a type layer that is **generated from the
authoritative schemata**, not hand-written. It is dependency-free (no Mathlib) and builds in
seconds.

**Blueprint (interactive):** <https://deicyde.github.io/wikifunctions/>

## Layout

```
├── Wikifunctions/Model/
│   ├── ZObject.lean          ← the hand-written substrate: the ZObject inductive
│   │                            (str | node), accessors, Z6/Z9 terminals, DecidableEq,
│   │                            WellFormed — all derived verbatim from §Z1/ZObjects
│   └── Types/                ← the GENERATED type layer: one module per built-in type
│       ├── Z4.lean  Z8.lean  Z17.lean  Z40.lean  …   (29 built-in types)
│       └── Z19677.lean                               (a community type, from live Z4)
├── codegen/gen_type.py       ← the compiler: type definition → Lean (see codegen/README.md)
├── blueprint/                ← the interactive blueprint (LaTeX → HTML graph + PDF)
└── lakefile.toml             ← no dependencies
```

## The compiler

Only three types are hand-written — `Z1`/ZObject and the `Z6`/`Z9` terminals it bottoms out in.
Every other built-in type is emitted by [`codegen/gen_type.py`](codegen/README.md) from its
authoritative definition (the function-schemata `CANONICAL/*.yaml`, or the live `Z4` for community
types), as a smart constructor + accessors + an `isZxx` recognizer + a `by decide` self-check on
the `ZObject` substrate. The schema *is* the spec, so the type layer is faithful by construction.

```bash
python3 codegen/gen_type.py Z40 Z8 Z17     # → Wikifunctions/Model/Types/{Z40,Z8,Z17}.lean
```

## Build

```bash
lake build          # dependency-free; ~30 jobs, no Mathlib cache needed
```

Everything is proved with no `sorry`. `Wikifunctions/Model/ZObject.lean` reproduces the spec's own
§Normal-form example (`natTwo`, the natural number 2) *definitionally*, and every generated type
carries a self-check that its constructor and recognizer agree.

## Status

The **object and type layers** are in place: the `ZObject` substrate with well-formedness, and all
29 built-in types generated. **Next:** the evaluator (`Z7` application over `ZObject`, returning a
real `Z22`/`Z5` result envelope), then functions and proofs on this substrate — at which point the
model connects to Mathlib oracles and re-establishes the verification results.

*History:* an earlier `Val`-based development (imperative-Python and composite-evaluator proofs) was
retired in favour of this spec-faithful rebuild; it remains in the git history.
