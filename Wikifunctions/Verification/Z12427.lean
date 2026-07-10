import Wikifunctions.Bridge.Z12427
import Wikifunctions.Verification.Contract

/-!
# Verification target for Wikifunction Z12427

This module turns the WikiLean/Mathlib oracle into the reusable evaluator contract that every
Z12427 implementation must satisfy.  The current live function has foreign Python/JavaScript
implementations, so no runtime is asserted to conform here.  Such a theorem requires a verified
foreign-language semantics or a future composition implementation.
-/

namespace Wikifunctions.Verification.Z12427

open Wikifunctions.Bridge
open Wikifunctions.Model
open Wikifunctions.Semantics

/-- The sole input key of Z12427. -/
def inputKey : Key := ⟨"Z12427K1", by decide⟩

/-- Revision-pinned typed projection of the live Z12427 signature. -/
def signature : FunctionSignature where
  inputs := [{ key := inputKey, valueSchema := Natural.checkedSchema }]
  output := Boolean.checkedSchema

/-- Typed implementation contract induced by the `@[wikidata Q49008]` Mathlib oracle. -/
def contract : Contract Nat Bool where
  functionId := IDs.z12427
  signature := signature
  signatureWellFormed := by decide
  encodeArguments value := [(inputKey, Natural.encode value)]
  argumentKeys _ := rfl
  argumentsSchemaValid value := by
    simp [signature, FunctionSignature.ArgumentsValid,
      FunctionSignature.acceptsArguments, FunctionSignature.lookupEvaluatedArgument,
      ZObject.keysNoDup]
  outputCodec := Boolean.codec
  outputSchema := rfl
  specification := Z12427_spec

/-- Any runtime satisfying the contract returns true exactly on Mathlib prime naturals. -/
theorem eval_eq_true_iff_of_conformsWithFuel
    (runtime : Runtime) (fuel : Nat → Nat)
    (h : ConformsWithFuel runtime contract fuel) (value : Nat) :
    eval runtime (fuel value) (contract.call value) = .value (Boolean.encode true) ↔
      Nat.Prime value := by
  rw [h.evaluates value]
  simp only [Outcome.value.injEq]
  change Boolean.encode (Z12427_spec value) = Boolean.encode true ↔ Nat.Prime value
  constructor
  · intro encoded
    exact z12427_spec_eq_true_iff value |>.mp (Boolean.codec.encode_injective encoded)
  · intro prime
    rw [z12427_spec_eq_true_iff value |>.mpr prime]

end Wikifunctions.Verification.Z12427
