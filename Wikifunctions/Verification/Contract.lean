import Wikifunctions.Bridge.Codec
import Wikifunctions.Semantics.Eval

/-!
# Reusable implementation contracts

An implementation proof should not identify a Wikidata tag with executable code.  It should state
that evaluating a particular Wikifunction call produces the encoding of a Lean specification.
`Contract` packages exactly the stable data needed by that statement; the runtime separately
chooses whether execution uses a composition, primitive, or foreign implementation.

Fuel is input-dependent in the general definition, so the same interface covers both finite
compositions and terminating recursive programs.  `ConformsWithFuel` records an explicit bound;
`Conforms` merely states termination and correctness for every input.
-/

namespace Wikifunctions.Verification

open Wikifunctions.Bridge
open Wikifunctions.Model
open Wikifunctions.Semantics

/-- A typed mathematical contract for one Wikifunction.

The encoded arguments are semantic values.  Their keys and revision-pinned schemas are fixed by
`signature`; every encoding is proved to satisfy those schemas.  The output codec carries its own
schema and is required to agree with the Z8 output projection. -/
structure Contract (Input Output : Type) where
  functionId : ZID
  signature : FunctionSignature
  signatureWellFormed : signature.WellFormed
  encodeArguments : Input → EvaluatedArguments
  argumentKeys :
    ∀ input, (encodeArguments input).map (fun entry => entry.1) = signature.inputKeys
  argumentsSchemaValid :
    ∀ input, signature.ArgumentsValid (encodeArguments input)
  outputCodec : Codec Output
  outputSchema : signature.output = outputCodec.schema
  specification : Input → Output

namespace Contract

/-- Lift already encoded argument values into literal composition expressions. -/
def callArguments (contract : Contract Input Output) (input : Input) : Arguments :=
  (contract.encodeArguments input).map fun entry => (entry.1, .literal entry.2)

/-- The closed Z7-style call whose evaluation is constrained by a contract. -/
def call (contract : Contract Input Output) (input : Input) : Expr :=
  .call (.literal (.reference contract.functionId)) (contract.callArguments input)

theorem callArgumentKeys (contract : Contract Input Output) (input : Input) :
    (contract.callArguments input).map (fun entry => entry.1) =
      contract.signature.inputKeys := by
  rw [← contract.argumentKeys input]
  simp [callArguments, List.map_map, Function.comp_def]

end Contract

/-- Correctness with a concrete, possibly input-dependent, fuel bound.

Besides extensional evaluation, conformance proves that the runtime entry is present and carries
the same typed signature as the mathematical contract.  A coincidentally correct result from a
registry entry with a different Z8 signature therefore cannot satisfy this judgment. -/
def ConformsWithFuel (runtime : Runtime) (contract : Contract Input Output)
    (fuel : Input → Nat) : Prop :=
  ∃ definition : FunctionDefinition,
    Registry.lookup runtime.registry contract.functionId = some definition ∧
    definition.signature = contract.signature ∧
    ∀ input,
      eval runtime (fuel input) (contract.call input) =
        .value (contract.outputCodec.encode (contract.specification input))

/-- Extensional correctness and termination, without fixing a complexity bound. -/
def Conforms (runtime : Runtime) (contract : Contract Input Output) : Prop :=
  ∃ definition : FunctionDefinition,
    Registry.lookup runtime.registry contract.functionId = some definition ∧
    definition.signature = contract.signature ∧
    ∀ input, ∃ fuel,
      eval runtime fuel (contract.call input) =
        .value (contract.outputCodec.encode (contract.specification input))

/-- Extract the pointwise evaluator theorem from a conformance witness. -/
theorem ConformsWithFuel.evaluates
    {Input Output : Type} {runtime : Runtime} {contract : Contract Input Output}
    {fuel : Input → Nat}
    (h : ConformsWithFuel runtime contract fuel) (input : Input) :
    eval runtime (fuel input) (contract.call input) =
      .value (contract.outputCodec.encode (contract.specification input)) := by
  rcases h with ⟨_, _, _, evaluates⟩
  exact evaluates input

/-- An explicit fuel proof immediately gives unbounded conformance. -/
theorem ConformsWithFuel.conforms
    {Input Output : Type} {runtime : Runtime} {contract : Contract Input Output}
    {fuel : Input → Nat}
    (h : ConformsWithFuel runtime contract fuel) : Conforms runtime contract := by
  rcases h with ⟨definition, hlookup, hsignature, evaluates⟩
  refine ⟨definition, hlookup, hsignature, ?_⟩
  intro input
  exact ⟨fuel input, evaluates input⟩

end Wikifunctions.Verification
