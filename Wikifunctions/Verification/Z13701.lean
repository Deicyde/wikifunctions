import Mathlib.Data.Nat.GCD.Basic
import Wikifunctions.Bridge.Boolean
import Wikifunctions.Bridge.Natural
import Wikifunctions.Semantics.Elaborate
import Wikifunctions.Verification.Contract

/-!
# Conformance of deployed composition Z13702

At the pinned live snapshot, Wikifunction Z13701 ("are coprime") has composition implementation
Z13702:

```
Z13522 (Z13612 (Z18 Z13701K1) (Z18 Z13701K2)) (Z13518 1)
```

Here Z13612 is interpreted by the strict contract `Nat.gcd`, and Z13522 by equality on the
proof-carrying Z13518 codec.  The theorem below therefore proves the composition itself correct
relative to those two leaf contracts.  It does not claim that every deployed implementation of
either leaf has already been verified.
-/

namespace Wikifunctions.Verification.Z13701

open Wikifunctions.Bridge
open Wikifunctions.Model
open Wikifunctions.Semantics

/-! ## Revision-pinned identifiers -/

def functionId : ZID := ⟨"Z13701", by decide⟩
def implementationId : ZID := ⟨"Z13702", by decide⟩
def gcdId : ZID := ⟨"Z13612", by decide⟩
def equalityId : ZID := ⟨"Z13522", by decide⟩

/-- Live revision from which the Z13701 signature and implementation list were read. -/
def functionRevision : Nat := 232866

/-- Live revision from which the Z13702 composition body was transcribed. -/
def implementationRevision : Nat := 139156

def firstInput : Key := ⟨"Z13701K1", by decide⟩
def secondInput : Key := ⟨"Z13701K2", by decide⟩
def gcdFirst : Key := ⟨"Z13612K1", by decide⟩
def gcdSecond : Key := ⟨"Z13612K2", by decide⟩
def equalityFirst : Key := ⟨"Z13522K1", by decide⟩
def equalitySecond : Key := ⟨"Z13522K2", by decide⟩

/-! ## The live composition body -/

/-- The semantic Z18 object used by the live body for a global input key. -/
def argumentObject (key : Key) : ZObject :=
  .object (.reference IDs.z18) [(Keys.z18k1, .string key.raw)]

/-- The nested Z13612 call exactly as stored in Z13702. -/
def gcdCallObject : ZObject :=
  .object (.reference IDs.z7)
    [(Keys.z7k1, .reference gcdId),
      (gcdFirst, argumentObject firstInput),
      (gcdSecond, argumentObject secondInput)]

/-- Semantic ZObject transcription of revision 139156's Z14K2 payload. -/
def liveBodyObject : ZObject :=
  .object (.reference IDs.z7)
    [(Keys.z7k1, .reference equalityId),
      (equalityFirst, gcdCallObject),
      (equalitySecond, Natural.encode 1)]

/-- Semantic transcription of the Z14K2 body stored in implementation Z13702. -/
def body : Expr :=
  .call (.literal (.reference equalityId))
    [(equalityFirst,
        .call (.literal (.reference gcdId))
          [(gcdFirst, .argument firstInput), (gcdSecond, .argument secondInput)]),
      (equalitySecond, .literal (Natural.encode 1))]

theorem liveBody_structurallyValid : liveBodyObject.StructurallyValid := by
  decide

theorem liveBody_schemaValid :
    Schema.Core.z7LiteralSchema.Valid liveBodyObject := by
  exact ⟨16, by decide⟩

/-- Decoding a semantic Z18 object preserves its global argument key. -/
theorem decode_argumentObject (fuel : Nat) (key : Key)
    (global : Schema.isGlobalKey key.raw = true) :
    Semantics.decode (fuel + 1) (argumentObject key) = .ok (.argument key) := by
  exact Semantics.decode_z18_argument_of_parse fuel key.raw key global (Key.parse_raw key)

theorem decode_gcdCallObject (fuel : Nat) :
    Semantics.decode (fuel + 2) gcdCallObject =
      .ok
        (.call (.literal (.reference gcdId))
          [(gcdFirst, .argument firstInput), (gcdSecond, .argument secondInput)]) := by
  have valid : gcdCallObject.structurallyValid = true := by decide
  dsimp [gcdCallObject] at valid
  have z7_ne_z18 : IDs.z7 ≠ IDs.z18 := by decide
  have gcdFirst_ne_callee : gcdFirst ≠ Keys.z7k1 := by decide
  have gcdSecond_ne_callee : gcdSecond ≠ Keys.z7k1 := by decide
  have firstGlobal : Schema.isGlobalKey firstInput.raw = true := by decide
  have secondGlobal : Schema.isGlobalKey secondInput.raw = true := by decide
  simp [gcdCallObject, Semantics.decode, valid, z7_ne_z18,
    Semantics.dynamicFields, Semantics.decodeDynamicArguments,
    Schema.T.field?, gcdFirst_ne_callee, gcdSecond_ne_callee,
    decode_argumentObject fuel firstInput firstGlobal,
    decode_argumentObject fuel secondInput secondGlobal]
  rfl

/-- The generic ZObject-to-expression decoder recovers the evaluator AST from the live body. -/
theorem decode_liveBody : Semantics.decode 8 liveBodyObject = .ok body := by
  have valid : liveBodyObject.structurallyValid = true := liveBody_structurallyValid
  dsimp [liveBodyObject] at valid
  have decodeOne : Semantics.decode 7 (Natural.encode 1) =
      .ok (.literal (Natural.encode 1)) := by
    have z13518_ne_z18 : IDs.z13518 ≠ IDs.z18 := by decide
    have z13518_ne_z7 : IDs.z13518 ≠ IDs.z7 := by decide
    simp [Semantics.decode, Natural.encode, ZObject.structurallyValid,
      ZObject.structurallyValidFields, ZObject.keysNoDup, z13518_ne_z18,
      z13518_ne_z7]
  have z7_ne_z18 : IDs.z7 ≠ IDs.z18 := by decide
  have equalityFirst_ne_callee : equalityFirst ≠ Keys.z7k1 := by decide
  have equalitySecond_ne_callee : equalitySecond ≠ Keys.z7k1 := by decide
  simp [liveBodyObject, body, Semantics.decode, valid, decodeOne, z7_ne_z18,
    Semantics.dynamicFields, Semantics.decodeDynamicArguments, Schema.T.field?,
    equalityFirst_ne_callee, equalitySecond_ne_callee, decode_gcdCallObject]
  rfl

/-- The complete semantic Z14 object whose Z14K2 field is the pinned live body. -/
def liveImplementationObject : ZObject :=
  Schema.Core.Z14.composition functionId liveBodyObject

/-- The persistent identities visible in the elaborated Z13702 composition. -/
def livePersistentCatalog : PersistentCatalog where
  contains id := id == functionId || id == equalityId || id == gcdId

/-- The generic persistent Z14 elaborator connects the pinned implementation object to the
evaluator AST. -/
theorem elaborate_liveImplementation :
    elaboratePersistentImplementation livePersistentCatalog 8 liveImplementationObject =
      .ok ⟨functionId, .composition body⟩ := by
  apply elaboratePersistentImplementation_composition
  · exact liveBody_structurallyValid
  · exact decode_liveBody
  · simp [livePersistentCatalog]
  · simp [PersistentCatalog.firstMissingExpression?, Expr.directReferences, body,
      livePersistentCatalog, Natural.encode]

/-- A proof-carrying snapshot of one persistent implementation artifact. -/
structure PinnedImplementation where
  implementationId : ZID
  revision : Nat
  object : ZObject
  elaborated : ElaboratedImplementation
  elaborates :
    elaboratePersistentImplementation livePersistentCatalog 8 object = .ok elaborated

/-- Revision 139156 of persistent object Z13702, paired with its checked elaboration. -/
def liveImplementation : PinnedImplementation where
  implementationId := implementationId
  revision := implementationRevision
  object := liveImplementationObject
  elaborated := ⟨functionId, .composition body⟩
  elaborates := elaborate_liveImplementation

/-! ## Revision-pinned typed signatures -/

def naturalSchema : Schema.Checked := Natural.checkedSchema

def booleanSchema : Schema.Checked := Boolean.checkedSchema

def coprimeSignature : FunctionSignature where
  inputs :=
    [{ key := firstInput, valueSchema := naturalSchema },
      { key := secondInput, valueSchema := naturalSchema }]
  output := booleanSchema

def gcdSignature : FunctionSignature where
  inputs :=
    [{ key := gcdFirst, valueSchema := naturalSchema },
      { key := gcdSecond, valueSchema := naturalSchema }]
  output := naturalSchema

def equalitySignature : FunctionSignature where
  inputs :=
    [{ key := equalityFirst, valueSchema := naturalSchema },
      { key := equalitySecond, valueSchema := naturalSchema }]
  output := booleanSchema

def coprimeDefinition : FunctionDefinition where
  signature := coprimeSignature
  implementations := [liveImplementation.elaborated.implementation]

def gcdDefinition : FunctionDefinition where
  signature := gcdSignature
  implementations := [.primitive (.strict gcdId)]

def equalityDefinition : FunctionDefinition where
  signature := equalitySignature
  implementations := [.primitive (.strict equalityId)]

/-- The minimal registry closure needed by Z13702. -/
def registry : Registry :=
  [(functionId, coprimeDefinition), (gcdId, gcdDefinition),
    (equalityId, equalityDefinition)]

theorem registry_wellFormed : Registry.WellFormed registry := by
  decide

/-! ## Mathlib-backed leaf contracts -/

/-- Look up an already evaluated keyed argument. -/
def lookupValue : EvaluatedArguments → Key → Option ZObject
  | [], _ => none
  | (candidate, value) :: arguments, key =>
      if candidate = key then some value else lookupValue arguments key

/-- Decode a keyed Z13518 natural argument. -/
def lookupNatural (arguments : EvaluatedArguments) (key : Key) : Option Nat :=
  (lookupValue arguments key).bind Natural.decode

/-- Strict denotations used by this proof: Z13612 is `Nat.gcd`; Z13522 is equality. -/
def strict : StrictDenotation := fun primitiveId arguments =>
  if primitiveId = gcdId then
    match lookupNatural arguments gcdFirst, lookupNatural arguments gcdSecond with
    | some left, some right => .ok (.literal (Natural.encode (Nat.gcd left right)))
    | _, _ => .error "Z13612 expects two Z13518 arguments"
  else if primitiveId = equalityId then
    match lookupNatural arguments equalityFirst, lookupNatural arguments equalitySecond with
    | some left, some right => .ok (.literal (Boolean.encode (decide (left = right))))
    | _, _ => .error "Z13522 expects two Z13518 arguments"
  else
    .error ("uninterpreted strict primitive " ++ primitiveId.raw)

/-- Foreign execution is deliberately outside this composition proof. -/
def rejectForeign : ForeignDenotation := fun code _ =>
  .error ("foreign execution disabled for language " ++ code.language.raw)

def runtime : Runtime where
  registry := registry
  policy := SelectionPolicy.compositionFirst
  resolve := fun _ => .ok none
  strict := strict
  foreign := rejectForeign

/-! ## Typed contract and correctness -/

/-- The Mathlib contract attached to Z13701. -/
def contract : Contract (Nat × Nat) Bool where
  functionId := functionId
  signature := coprimeSignature
  signatureWellFormed := by decide
  encodeArguments input :=
    [(firstInput, Natural.encode input.1), (secondInput, Natural.encode input.2)]
  argumentKeys _ := rfl
  argumentsSchemaValid input := by
    simp [coprimeSignature, naturalSchema, FunctionSignature.ArgumentsValid,
      FunctionSignature.acceptsArguments, FunctionSignature.lookupEvaluatedArgument,
      ZObject.keysNoDup, firstInput, secondInput]
  outputCodec := Boolean.codec
  outputSchema := rfl
  specification input := decide (Nat.Coprime input.1 input.2)

@[simp]
theorem eval_literal_natural_encode (runtime : Runtime) (fuel value : Nat) :
    eval runtime (fuel + 1) (.literal (Natural.encode value)) =
      .value (Natural.encode value) := by
  simp [Natural.encode]

@[simp]
theorem eval_literal_boolean_encode (runtime : Runtime) (fuel : Nat) (value : Bool) :
    eval runtime (fuel + 1) (.literal (Boolean.encode value)) =
      .value (Boolean.encode value) := by
  simp [Boolean.encode]

/-- Evaluation of the actual Z13702 body agrees with Mathlib's `Nat.Coprime`. -/
theorem eval_contract (left right : Nat) :
    eval runtime 7 (contract.call (left, right)) =
      .value (Boolean.encode (decide (Nat.Coprime left right))) := by
  simp [Contract.call, Contract.callArguments, contract, runtime, registry,
    coprimeDefinition, gcdDefinition, equalityDefinition, liveImplementation, body, eval,
    Expr.instantiate,
    coprimeSignature, gcdSignature, equalitySignature, naturalSchema, booleanSchema,
    FunctionSignature.inputKeys, FunctionSignature.acceptsArguments,
    FunctionSignature.lookupEvaluatedArgument, ZObject.keysNoDup, validateOutput,
    validateArguments, firstDuplicateArgument?, firstMissingArgument?,
    firstUnexpectedArgument?, containsArgument, SelectionPolicy.compositionFirst,
    SelectionPolicy.select, SelectionPolicy.selectFromOrder, SelectionPolicy.firstOfKind,
    Implementation.kind, evalPrimitive, evaluateArguments, strict, lookupNatural, lookupValue,
    functionId, gcdId, equalityId, firstInput, secondInput, gcdFirst, gcdSecond,
    equalityFirst, equalitySecond, Nat.Coprime]

/-- Z13702 has a uniform finite fuel bound, hence satisfies the reusable contract. -/
theorem conformsWithFuel : ConformsWithFuel runtime contract (fun _ => 7) := by
  refine ⟨coprimeDefinition, rfl, rfl, ?_⟩
  intro input
  exact eval_contract input.1 input.2

theorem conforms : Conforms runtime contract := conformsWithFuel.conforms

/-- The evaluated composition returns true exactly for coprime natural numbers. -/
theorem eval_eq_true_iff (left right : Nat) :
    eval runtime 7 (contract.call (left, right)) = .value (Boolean.encode true) ↔
      Nat.Coprime left right := by
  rw [eval_contract]
  constructor
  · intro h
    have encoded :
        Boolean.codec.encode (decide (Nat.Coprime left right)) =
          Boolean.codec.encode true := by
      simpa [Boolean.codec] using Outcome.value.inj h
    exact decide_eq_true_eq.mp (Boolean.codec.encode_injective encoded)
  · intro h
    rw [decide_eq_true_eq.mpr h]

end Wikifunctions.Verification.Z13701
