import Wikifunctions.Semantics.Decode

/-!
# Elaborating Z14 implementations

This module is the checked boundary between the pre-resolved direct-ID subset of semantic
Z14/Z16 values and the evaluator's `Implementation` type.  Literal/transient Z8 identities and
literal Z61 languages require a richer identity representation and are deliberately not coerced
to ZIDs here.  Within the supported persistent subset this is stricter than a generic projection:

* a Z14 must contain a function reference and exactly one of Z14K2, Z14K3, or Z14K4;
* a composition body is decoded by the shared expression decoder;
* a builtin identifier must pass the validated `ZID.parse` boundary;
* a persistent catalog proves that direct global IDs exist in the pinned snapshot;
* a Z16 must contain exactly one language reference and one source string; and
* structural invalidity, including duplicate fields, is rejected before projection.

Field order is not significant.  The returned record retains the Z14K1 function identity so a
caller can check that an implementation belongs to the registry entry under construction.
-/

namespace Wikifunctions.Semantics

open Wikifunctions.Model

@[simp] private theorem z1k1_ne_z14k1 : Keys.z1k1 ≠ Keys.z14k1 := by decide
@[simp] private theorem z1k1_ne_z14k2 : Keys.z1k1 ≠ Keys.z14k2 := by decide
@[simp] private theorem z1k1_ne_z14k3 : Keys.z1k1 ≠ Keys.z14k3 := by decide
@[simp] private theorem z1k1_ne_z14k4 : Keys.z1k1 ≠ Keys.z14k4 := by decide
@[simp] private theorem z1k1_ne_z16k1 : Keys.z1k1 ≠ Keys.z16k1 := by decide
@[simp] private theorem z1k1_ne_z16k2 : Keys.z1k1 ≠ Keys.z16k2 := by decide
@[simp] private theorem z14k1_ne_z14k2 : Keys.z14k1 ≠ Keys.z14k2 := by decide
@[simp] private theorem z14k1_ne_z14k3 : Keys.z14k1 ≠ Keys.z14k3 := by decide
@[simp] private theorem z14k1_ne_z14k4 : Keys.z14k1 ≠ Keys.z14k4 := by decide
@[simp] private theorem z14k2_ne_z14k3 : Keys.z14k2 ≠ Keys.z14k3 := by decide
@[simp] private theorem z14k2_ne_z14k4 : Keys.z14k2 ≠ Keys.z14k4 := by decide
@[simp] private theorem z14k3_ne_z14k2 : Keys.z14k3 ≠ Keys.z14k2 := by decide
@[simp] private theorem z14k3_ne_z14k4 : Keys.z14k3 ≠ Keys.z14k4 := by decide
@[simp] private theorem z16k1_ne_z16k2 : Keys.z16k1 ≠ Keys.z16k2 := by decide

/-- Failures while converting semantic Z14/Z16 values into evaluator implementations. -/
inductive ImplementationError where
  | structurallyInvalid
  | expectedZ14
  | malformedFunctionId
  | invalidAlternativeSet
  | malformedCode
  | malformedBuiltin
  | invalidBuiltinId (raw : String)
  | nonPersistentIdentifier (id : ZID)
  | expressionDecode (error : DecodeError)
deriving Repr, DecidableEq

/-- An evaluator implementation together with the Z14K1 function identity it implements. -/
structure ElaboratedImplementation where
  functionId : ZID
  implementation : Implementation
deriving Repr

namespace Expr

/-- Literal reference expressions whose identities are visible to the current evaluator.

The traversal follows calls and their arguments but deliberately does not recurse into the fields
of a literal `ZObject`: resolving references inside arbitrary object fields is a separate,
documented extension of the evaluator.  Quotes remain opaque. -/
def directReferences : Expr → List ZID
  | .literal (.reference id) => [id]
  | .literal _ => []
  | .argument _ => []
  | .quote _ => []
  | .call callee arguments =>
      directReferences callee ++ arguments.flatMap fun entry => directReferences entry.2
termination_by expression => sizeOf expression
decreasing_by
  · simp +arith
  · have hentry : sizeOf entry < sizeOf arguments := by
      apply List.sizeOf_lt_of_mem
      assumption
    have hsnd : sizeOf entry.2 < sizeOf entry := by
      cases entry
      simp +arith
    have hlist : sizeOf arguments < sizeOf (Expr.call callee arguments) := by
      simp +arith
    exact Nat.lt_trans hsnd (Nat.lt_trans hentry hlist)

end Expr

/-- Revision-pinned evidence that a ZID names an available persistent object.

Lexical `ZID.parse` alone cannot establish existence.  Production elaboration therefore receives
this catalog from the same snapshot as the implementation objects. -/
structure PersistentCatalog where
  contains : ZID → Bool

namespace PersistentCatalog

/-- Return the first evaluator-visible reference in an expression that is absent from the pinned
catalog. -/
def firstMissingExpression? (catalog : PersistentCatalog) (expression : Expr) : Option ZID :=
  expression.directReferences.find? fun id => !catalog.contains id

/-- Return the first global identity missing from the pinned catalog. -/
def firstMissing? (catalog : PersistentCatalog) (value : ElaboratedImplementation) : Option ZID :=
  if !catalog.contains value.functionId then
    some value.functionId
  else
    match value.implementation with
    | .composition body => catalog.firstMissingExpression? body
    | .primitive (.strict builtinId) =>
        if catalog.contains builtinId then none else some builtinId
    | .primitive (.lazyIf _ _ _) => none
    | .foreign code =>
        if catalog.contains code.language then none else some code.language

/-- Check every persistent identity used directly by an elaborated implementation. -/
def accepts (catalog : PersistentCatalog) (value : ElaboratedImplementation) : Bool :=
  (catalog.firstMissing? value).isNone

end PersistentCatalog

/-- Decode a literal Z16 code value.

The length check and structural-validity check make this an exact, order-independent decoder:
additional, missing, or duplicate fields cannot be silently ignored. -/
def decodeForeignCode (value : ZObject) : Except ImplementationError ForeignCode :=
  if value.structurallyValid then
    match value with
    | .object (.reference typeId) fields =>
        if typeId = IDs.z16 && fields.length = 2 then
          match Schema.T.field? fields Keys.z16k1, Schema.T.field? fields Keys.z16k2 with
          | some (.reference language), some (.string source) => .ok ⟨language, source⟩
          | _, _ => .error .malformedCode
        else
          .error .malformedCode
    | _ => .error .malformedCode
  else
    .error .structurallyInvalid

/-- Decode the exactly-one Z14 implementation alternative after structural validation. -/
private def decodeImplementationAlternative (fuel : Nat) (fields : List (Key × ZObject)) :
    Except ImplementationError Implementation :=
  match Schema.T.field? fields Keys.z14k2, Schema.T.field? fields Keys.z14k3,
      Schema.T.field? fields Keys.z14k4 with
  | some body, none, none =>
      match decode fuel body with
      | .ok expression => .ok (.composition expression)
      | .error error => .error (.expressionDecode error)
  | none, some code, none =>
      match decodeForeignCode code with
      | .ok foreignCode => .ok (.foreign foreignCode)
      | .error error => .error error
  | none, none, some (.string raw) =>
      match ZID.parse raw with
      | some builtinId => .ok (.primitive (.strict builtinId))
      | none => .error (.invalidBuiltinId raw)
  | none, none, some _ => .error .malformedBuiltin
  | _, _, _ => .error .invalidAlternativeSet

/-- Elaborate one literal semantic Z14 object.

Exactly two data fields are required: Z14K1 and one implementation alternative.  Combined with
structural key uniqueness, this rules out unknown extra fields as well as duplicate alternatives.
The fuel parameter is passed unchanged to composition-expression decoding. -/
def elaborateImplementation (fuel : Nat) (value : ZObject) :
    Except ImplementationError ElaboratedImplementation :=
  if value.structurallyValid then
    match value with
    | .object (.reference typeId) fields =>
        if typeId = IDs.z14 then
          match Schema.T.field? fields Keys.z14k1 with
          | some (.reference functionId) =>
              if fields.length = 2 then
                match decodeImplementationAlternative fuel fields with
                | .ok implementation => .ok ⟨functionId, implementation⟩
                | .error error => .error error
              else
                .error .invalidAlternativeSet
          | _ => .error .malformedFunctionId
        else
          .error .expectedZ14
    | _ => .error .expectedZ14
  else
    .error .structurallyInvalid

/-- Elaborate the pre-resolved direct-ID subset and verify that every resulting global identity
exists in the revision-pinned persistent catalog. -/
def elaboratePersistentImplementation (catalog : PersistentCatalog) (fuel : Nat)
    (value : ZObject) : Except ImplementationError ElaboratedImplementation :=
  match elaborateImplementation fuel value with
  | .error error => .error error
  | .ok elaborated =>
      match catalog.firstMissing? elaborated with
      | none => .ok elaborated
      | some id => .error (.nonPersistentIdentifier id)

/-! ## Constructor correctness -/

/-- A well-formed composition constructor elaborates to the expression produced by `decode`. -/
theorem elaborateImplementation_composition (fuel : Nat) (functionId : ZID)
    (body : ZObject) (expression : Expr) (hvalid : body.structurallyValid = true)
    (hdecode : decode fuel body = .ok expression) :
    elaborateImplementation fuel (Schema.Core.Z14.composition functionId body) =
      .ok ⟨functionId, .composition expression⟩ := by
  simp [elaborateImplementation, Schema.Core.Z14.composition,
    decodeImplementationAlternative, Schema.T.field?, ZObject.structurallyValid,
    ZObject.structurallyValidFields, ZObject.keysNoDup, hvalid, hdecode]

/-- A literal Z16 constructor decodes to the corresponding foreign-code record. -/
theorem decodeForeignCode_code (language : ZID) (source : String) :
    decodeForeignCode (Schema.Core.Z16.code language source) = .ok ⟨language, source⟩ := by
  simp [decodeForeignCode, Schema.Core.Z16.code, Schema.T.field?,
    ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup]

/-- A code implementation constructor elaborates to an evaluator foreign implementation. -/
theorem elaborateImplementation_code (fuel : Nat) (functionId language : ZID)
    (source : String) :
    elaborateImplementation fuel
        (Schema.Core.Z14.code functionId (Schema.Core.Z16.code language source)) =
      .ok ⟨functionId, .foreign ⟨language, source⟩⟩ := by
  simp [elaborateImplementation, Schema.Core.Z14.code,
    Schema.Core.Z16.code, decodeImplementationAlternative, Schema.T.field?,
    ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup,
    decodeForeignCode]

/-- A validated persistent builtin ZID elaborates to a strict primitive. -/
theorem elaborateImplementation_builtin (fuel : Nat) (functionId builtinId : ZID) :
    elaborateImplementation fuel (Schema.Core.Z14.builtin functionId builtinId) =
      .ok ⟨functionId, .primitive (.strict builtinId)⟩ := by
  simp [elaborateImplementation, Schema.Core.Z14.builtin,
    decodeImplementationAlternative, Schema.T.field?, ZObject.structurallyValid,
    ZObject.structurallyValidFields, ZObject.keysNoDup]

/-- Persistent elaboration of a composition requires its function identity in the catalog. -/
theorem elaboratePersistentImplementation_composition (catalog : PersistentCatalog)
    (fuel : Nat) (functionId : ZID) (body : ZObject) (expression : Expr)
    (hvalid : body.structurallyValid = true)
    (hdecode : decode fuel body = .ok expression)
    (hfunction : catalog.contains functionId = true)
    (hreferences : catalog.firstMissingExpression? expression = none) :
    elaboratePersistentImplementation catalog fuel
        (Schema.Core.Z14.composition functionId body) =
      .ok ⟨functionId, .composition expression⟩ := by
  simp [elaboratePersistentImplementation,
    elaborateImplementation_composition fuel functionId body expression hvalid hdecode,
    PersistentCatalog.firstMissing?, hfunction, hreferences]

/-- Persistent builtin elaboration checks both the implemented function and builtin identities. -/
theorem elaboratePersistentImplementation_builtin (catalog : PersistentCatalog)
    (fuel : Nat) (functionId builtinId : ZID)
    (hfunction : catalog.contains functionId = true)
    (hbuiltin : catalog.contains builtinId = true) :
    elaboratePersistentImplementation catalog fuel
        (Schema.Core.Z14.builtin functionId builtinId) =
      .ok ⟨functionId, .primitive (.strict builtinId)⟩ := by
  simp [elaboratePersistentImplementation, elaborateImplementation_builtin,
    PersistentCatalog.firstMissing?, hfunction, hbuiltin]

/-! ## Rejection laws -/

/-- Duplicate Z14K1 fields are rejected before a function identity is projected. -/
theorem elaborateImplementation_duplicate_function_rejected (fuel : Nat)
    (functionId builtinId : ZID) :
    elaborateImplementation fuel
        (.object (.reference IDs.z14)
          [(Keys.z14k1, .reference functionId),
            (Keys.z14k1, .reference functionId),
            (Keys.z14k4, .string builtinId.raw)]) =
      .error .structurallyInvalid := by
  simp [elaborateImplementation, ZObject.structurallyValid,
    ZObject.structurallyValidFields, ZObject.keysNoDup]

/-- Supplying two mutually exclusive Z14 alternatives is rejected. -/
theorem elaborateImplementation_multiple_alternatives_rejected (fuel : Nat)
    (functionId builtinId : ZID) (body : ZObject)
    (hvalid : body.structurallyValid = true) :
    elaborateImplementation fuel
        (.object (.reference IDs.z14)
          [(Keys.z14k1, .reference functionId), (Keys.z14k2, body),
            (Keys.z14k4, .string builtinId.raw)]) =
      .error .invalidAlternativeSet := by
  simp [elaborateImplementation, Schema.T.field?, ZObject.structurallyValid,
    ZObject.structurallyValidFields, ZObject.keysNoDup, hvalid]

/-- Duplicate Z16 fields are rejected, rather than resolved by a first-field-wins policy. -/
theorem decodeForeignCode_duplicate_language_rejected (language : ZID) (source : String) :
    decodeForeignCode
        (.object (.reference IDs.z16)
          [(Keys.z16k1, .reference language), (Keys.z16k1, .reference language),
            (Keys.z16k2, .string source)]) =
      .error .structurallyInvalid := by
  simp [decodeForeignCode, ZObject.structurallyValid,
    ZObject.structurallyValidFields, ZObject.keysNoDup]

/-- A non-ZID builtin string cannot enter the evaluator's validated primitive identifier. -/
theorem elaborateImplementation_invalid_builtin_rejected (fuel : Nat) (functionId : ZID) :
    elaborateImplementation fuel
        (.object (.reference IDs.z14)
          [(Keys.z14k1, .reference functionId), (Keys.z14k4, .string "not-a-zid")]) =
      .error (.invalidBuiltinId "not-a-zid") := by
  simp [elaborateImplementation, decodeImplementationAlternative, Schema.T.field?,
    ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup,
    ZID.parse, isZID]

/-- Wrongly typed Z16 source fields are rejected as malformed code. -/
theorem decodeForeignCode_malformed_source_rejected (language sourceId : ZID) :
    decodeForeignCode
        (.object (.reference IDs.z16)
          [(Keys.z16k1, .reference language), (Keys.z16k2, .reference sourceId)]) =
      .error .malformedCode := by
  simp [decodeForeignCode, Schema.T.field?, ZObject.structurallyValid,
    ZObject.structurallyValidFields, ZObject.keysNoDup]

end Wikifunctions.Semantics
