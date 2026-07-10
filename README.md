# Wikifunctions in Lean

This repository is an auditable Lean 4 core for the
[Wikifunctions function model](https://www.wikifunctions.org/wiki/Wikifunctions:Function_model).
It is designed to state reusable mathematical contracts and prove that a particular, pinned
Wikifunctions implementation satisfies them.

The strongest end-to-end result currently proved is the transcribed Z13702 composition for
Z13701 (“are coprime”), relative to explicit Mathlib-backed contracts for its `gcd` and equality
leaves. The Z12427 (“is prime”) bridge states the desired Mathlib theorem, but deliberately does
not claim that its deployed Python or JavaScript bodies have been verified.

## The Z12427 target

Mathlib's `Nat.Prime` carries `@[wikidata Q49008]`; the metadata bridge records the join from
Q49008 to Wikifunction Z12427. The mathematical oracle is:

```lean
def Z12427_spec (value : Nat) : Bool :=
  decide (Nat.Prime value)

theorem z12427_spec_eq_true_iff (value : Nat) :
    Z12427_spec value = true ↔ Nat.Prime value
```

`Verification.Z12427.contract` adds the pinned Z13518 input schema, Z40 output schema, codecs,
function identity, and registry-signature equality. Consequently,
`eval_eq_true_iff_of_conformsWithFuel` proves that any conforming runtime returns encoded true
exactly for prime naturals. A Wikidata tag discovers the intended concept; conformance is the
separate correctness proof. The root build runs `CrossRef.assertMathlibTag`, so the pinned build
fails if Mathlib no longer exposes `Q49008` on `Nat.Prime`.

## Architecture

```text
Wikifunctions/Model/
  ZObject.lean          validated IDs/keys, semantic values, lossless raw quote payloads
  Serialization.lean   distinct semantic canonical and normal rendering
  Decode.lean          exact serializer-image decoding and proved round trips
  Ingest.lean          order-independent, fuelled JSON ingestion
  Schema.lean          executable schema IR, explicit validation fuel, pinned schemas

Wikifunctions/Semantics/
  Eval.lean             inner Z7/Z18 evaluator, stores/resolvers, laziness, selection, fuel
  Decode.lean           semantic ZObject-to-expression decoding
  Elaborate.lean        checked persistent-ID Z14/Z16-to-Implementation elaboration
  Result.lean           public Z22 wrapper and proof-carrying failure-metadata boundary

Wikifunctions/Bridge/
  Codec.lean            schema-carrying proof interface for Lean ↔ ZObject codecs
  Natural.lean          deployed Z13518 ↔ Nat
  Boolean.lean          deployed full Z40 values ↔ Bool
  Z12427.lean           Mathlib prime oracle and revision metadata
  CrossRef.lean         exporter for Mathlib @[wikidata] metadata

Wikifunctions/Verification/
  Contract.lean         typed signature-linked evaluator conformance
  Z12427.lean           implementation obligation for “is prime”
  Z13701.lean           pinned Z13702 composition proof, relative to leaf contracts
```

The semantic inductive is intentionally permissive. Validity remains visible through separate
judgments:

- `StructurallyValid` enforces ordinary-object key uniqueness and recursive shape, but treats a
  Z99 raw payload as opaque;
- `Schema.Checked.Valid` executes a pinned type schema at an explicit fuel bound;
- `NormalWireSafe` and `CanonicalWireSafe` state the constructor-disjointness needed for exact
  renderer/decoder round trips; and
- `FunctionSignature` and `Contract` connect Z17/Z8-style input/output schemas to encoded values
  and to the selected runtime registry entry.

## Wire and quote boundaries

`Raw` preserves object order, duplicate keys, arrays, strings, number spelling, booleans, and
null. A `ZObject.quote` contains `Raw`, so a malformed call can be ingested and reproduced without
being decoded, sorted, validated, or resolved.

There are two decoder APIs for different claims:

- `decodeNormal` and `decodeCanonical` recognize the exact images emitted by this project's
  renderers; their left-inverse theorems are proved on the explicit wire-safe domain.
- `ingestNormal` and `ingestCanonical` are the external JSON boundary. They reject duplicates,
  look fields up by name, sort ordinary data fields deterministically, accept reordered Z1K1 and
  Z881 cells (including recursive literal Z4/Z8 identities), and preserve quoted payloads exactly.

This split keeps the round-trip theorem small without incorrectly treating JSON object order as
semantic.

## Composition semantics

`Semantics.eval` is the inner value evaluator. It has:

- expression-valued Z7 callees and keyed Z18 references;
- call-by-name composition substitution and an evaluator-aware lazy conditional;
- strict/foreign input schemas matched by key rather than object-member order, plus output-schema
  checks before returning;
- open ZID registries and deterministic, explicit implementation-selection policy;
- all three Z14 alternatives for pre-resolved persistent-ID objects after checked elaboration:
  composition, builtin/strict primitive, and foreign code;
- a finite `PersistentStore` projection and an open `ReferenceResolver`; reference chains consume
  one unit of fuel per replacement, while literal function heads remain identities for registry
  dispatch; and
- distinct semantic errors and out-of-fuel.

Strict and foreign denotations, persistent lookup, and selection are runtime fields—not hidden
Lean axioms. Successful strict/foreign adapters return evaluator expressions and therefore
re-enter evaluation rather than being accepted before a fixpoint. `Semantics.execute` is the
public layer: it checks a returned value and wraps success in Z22; failure puts Z24/Void in Z22K1
and caller-supplied, schema-checked failure metadata in Z22K2. The concrete evolving metadata/Z5
map remains an explicit proof obligation for any `ResultProtocol` instance.

The Z13702 proof follows this path:

```text
live semantic Z14 object
  → schema check
  → generic Z14 elaboration
  → generic ZObject expression decoding
  → fuelled composition evaluation
  → schema-carrying Bool codec
  → Nat.Coprime theorem
```

The live body is:

```text
Z13522 (Z13612 (Z18 Z13701K1) (Z18 Z13701K2)) (Z13518 1)
```

The proof interprets Z13612 as `Nat.gcd` and Z13522 as equality on naturals. Those leaf
denotations are stated assumptions with their own future implementation-conformance obligations.

## Exact trust boundary

| Boundary | What is proved now |
| --- | --- |
| Composition core | Executable inner semantics, named laws, Z14 elaboration, and the pinned Z13702 proof |
| Types and codecs | Executable schemas on inputs/outputs; codecs and contracts carry validity proofs |
| Persistent references | Fuelled top-level chains and an explicit decoded Z2K2 store/resolver interface |
| Public result | Z22 construction and validity; failures use Z24 plus schema-checked metadata |
| Builtin leaves | Extensible denotations; each deployed leaf still needs conformance |
| Python/JavaScript | Explicit foreign boundary; no deployed-code correctness claim |
| JSON | Exact renderer round trips plus separate order-independent ingestion |
| Wikidata tags | Discovery metadata only, never correctness evidence |

Important remaining extensions are deliberately visible:

- a complete live Z4/Z8/Z17 registry and type-directed resolution inside arbitrary object fields,
  including the Z2-as-argument exception;
- runtime-wide schema enforcement for arbitrary nested composition/lazy calls (strict and foreign
  boundaries check input/output schemas; contracts prove validity on their own typed domain);
- literal/transient Z8 function identities and literal Z61 language values in elaboration (the
  current executable path is the common pre-resolved persistent-ID subset);
- a concrete, revision-pinned production metadata map containing typed Z5 errors;
- equivalence between this deterministic strategy and any chosen production evaluator strategy;
- verified semantics or proof-producing translation for deployed Python and JavaScript; and
- conformance proofs for strict leaf implementations used by composition theorems.

These are not assumptions of the current theorems; they delimit which production executions can
currently instantiate a conformance contract.

## Build and audit

The project pins Lean and Mathlib.

```bash
lake update
lake exe cache get
lake build
lake env lean Wikifunctions/Audit.lean
python3 blueprint/check_decls.py
```

CI rejects `sorry`, `admit`, custom `axiom` declarations, and `native_decide`. `Audit.lean` prints
the axiom dependencies of the load-bearing theorems; expected Lean/Mathlib foundations remain
visible.

The interactive blueprint is published at
[deicyde.github.io/wikifunctions](https://deicyde.github.io/wikifunctions/). Structural schemas
are pinned to
[function-schemata commit 40db6bc](https://gitlab.wikimedia.org/repos/abstract-wiki/wikifunctions/function-schemata/-/tree/40db6bc971df332a562de6080e6cb418ef813437),
and WikiLean integration is documented at
[wikilean.jackmccarthy.org/wikifunctions](https://wikilean.jackmccarthy.org/wikifunctions).
