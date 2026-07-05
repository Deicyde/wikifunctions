# `codegen` — the type compiler

The ground-up rebuild **generates** the per-type Lean rather than hand-writing it. Only a
handful of types are hand-written — `Z1`/ZObject itself and the `Z6`/`Z9` terminals it bottoms
out in ([`Wikifunctions/Model/ZObject.lean`](../Wikifunctions/Model/ZObject.lean)). Every other
type is emitted by `gen_type.py` from its authoritative definition.

## What it reads

A type's definition comes from whichever authority defines it, both reduced to the same shape
— `{type ZID, ordered data keys}` (everything but the universal `Z1K1`):

- **built-in types** → the function-schemata JSON-Schema
  `data/CANONICAL/<ZID>.yaml` (`<ZID>_literal.properties` lists the keys);
- **community types** → the live `Z4` definition via `wikilambda_fetch`
  (`Z2K2.Z4K2` lists the keys as `Z3` objects).

The schemata YAML is tried first; the live `Z4` is the fallback for types with no schema.

## What it emits

For a type `Zxx` with data keys `ZxxK1 … ZxxKn`, into `Wikifunctions/Model/Types/<ZID>.lean`:

```lean
def Zxx.mk (zxxk1 … : ZObject) : ZObject := node [("Z1K1", reference "Zxx"), ("ZxxK1", zxxk1), …]
def Zxx.ZxxK1? (z : ZObject) : Option ZObject := z.get? "ZxxK1"          -- one per key
def isZxx (z : ZObject) : Bool := z.typeId? == some "Zxx" && (z.get? "ZxxK1").isSome && …
example : isZxx (Zxx.mk …) = true := by decide                          -- baked-in self-check
```

Everything is in terms of the hand-written `ZObject` primitives, so the output is faithful by
construction: no per-type interpretation, and the self-check proves the constructor and
recognizer agree.

## Use

```bash
python3 codegen/gen_type.py Z40 Z17 Z19677     # -> Wikifunctions/Model/Types/{Z40,Z17,Z19677}.lean
lake build Wikifunctions.Model.Types.Z40       # generated modules build on the ZObject substrate
```

Requires `pyyaml` (`pip install pyyaml`). Generated files **are committed** — they are the type
layer other modules import — and are regenerable at any time; they carry an "AUTO-GENERATED, do
not edit" header.

## Status / next

Proven on `Z40` (from schemata YAML) and `Z19677` (from live `Z4`) — both build green. Next: run
it across the built-in inventory (`Z4`, `Z8`, `Z17`, `Z14`, `Z16`, …) and the community numeric
types, then thread enum/type constraints from the schema into a richer `isZxx` (e.g. `Z40K1 ∈
{Z41, Z42}`), which the current version checks only for key *presence*.
