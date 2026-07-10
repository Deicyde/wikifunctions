import Mathlib.Data.Nat.Prime.Defs
import Wikifunctions.Bridge.Boolean
import Wikifunctions.Bridge.Natural

/-!
# The formal specification associated with Z12427

This file deliberately defines only the mathematical oracle and concept metadata.  It does not
assert that any deployed Python or JavaScript implementation computes this oracle.  That claim
must eventually be mediated by evaluator semantics and a separate implementation proof.
-/

namespace Wikifunctions.Bridge

open Model

/-- The Mathlib oracle intended for Wikifunction Z12427 (`is prime`). -/
def Z12427_spec (value : Nat) : Bool :=
  decide (Nat.Prime value)

@[simp]
theorem z12427_spec_eq_true_iff (value : Nat) : Z12427_spec value = true ↔ Nat.Prime value := by
  simp [Z12427_spec]

/-- Executable semantic-object contract for Z12427.

This oracle decodes the canonical Z13518 input and encodes the Mathlib specification result as a
Z40 value.  It is an implementation contract, not a claim that any deployed Python or JavaScript
implementation conforms to that contract. -/
def Z12427_oracle (input : ZObject) : Option ZObject := do
  let value ← Natural.decode input
  pure (Boolean.encode (Z12427_spec value))

/-- Evaluation of the semantic-object oracle on a canonical Z13518 input. -/
@[simp]
theorem z12427_oracle_encode (value : Nat) :
    Z12427_oracle (Natural.encode value) = some (Boolean.encode (Z12427_spec value)) := by
  simp [Z12427_oracle]

/-- On canonical Z13518 inputs, the semantic-object oracle returns encoded true exactly for
Mathlib prime naturals. -/
theorem z12427_oracle_encode_eq_true_iff (value : Nat) :
    Z12427_oracle (Natural.encode value) = some (Boolean.encode true) ↔ Nat.Prime value := by
  rw [z12427_oracle_encode]
  simp only [Option.some.injEq]
  constructor
  · intro h
    exact (z12427_spec_eq_true_iff value).mp (Boolean.codec.encode_injective h)
  · intro h
    rw [(z12427_spec_eq_true_iff value).mpr h]

/-! ## Metadata, kept separate from correctness -/

/-- An auditable metadata join between an external concept, a Wikifunction, and a Lean name.

This structure carries identifiers and source revisions, not a proof that executable code is
correct.  The revisions identify the snapshots from which the external part of the join was
read. -/
structure ConceptMetadata where
  wikidataItem : String
  wikifunction : ZID
  leanDeclaration : Lean.Name
  wikidataRevision : Nat
  wikifunctionRevision : Nat
deriving Repr, DecidableEq

/-- Q49008 is linked to Z12427 by the Wikidata sitelink, while `Nat.Prime` carries
`@[wikidata Q49008]` in the pinned Mathlib revision.

External snapshots: Wikidata Q49008 revision 2513187771 and Wikifunctions Z12427 revision
286624. -/
def primeConceptMetadata : ConceptMetadata where
  wikidataItem := "Q49008"
  wikifunction := IDs.z12427
  leanDeclaration := ``Nat.Prime
  wikidataRevision := 2513187771
  wikifunctionRevision := 286624

end Wikifunctions.Bridge
