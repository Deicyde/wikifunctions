import Wikifunctions.Model.Schema
import Wikifunctions.Semantics.Eval

/-!
# Public Z22 evaluation results

`Semantics.eval` is the inner value evaluator used by composition proofs.  The public
Wikifunctions protocol wraps it in Z22/Evaluation result.  A failed Z22 has Z24/Void in Z22K1;
its Z5 error belongs inside the Z22K2 metadata map.  The production metadata shape evolves, so
this module makes success metadata and failure-metadata construction explicit proof-carrying
inputs rather than hard-coding one backend snapshot.
-/

namespace Wikifunctions.Semantics

open Wikifunctions.Model

/-- Failures that the public metadata layer must describe. -/
inductive EvaluationFailure where
  | semantic (error : EvalError)
  | outOfFuel
  | invalidRuntimeValue (value : ZObject)
deriving Repr

/-- Proof-carrying, revision-sensitive metadata needed to construct public Z22 results.

The failure encoder produces the entire Z22K2 metadata object, not a value for Z22K1.  This core
checks it against a caller-supplied schema; a concrete integration must instantiate that schema
with the revision-pinned metadata map and its typed Z5 error entry. -/
structure ResultProtocol where
  successMetadata : ZObject
  successMetadataValid : successMetadata.StructurallyValid
  failureMetadataSchema : Schema.Checked
  encodeFailureMetadata : EvaluationFailure → ZObject
  failureMetadataValid :
    ∀ failure, failureMetadataSchema.Valid (encodeFailureMetadata failure)

/-- Wrap an inner evaluator outcome in the public Z22 protocol.

Successful runtime values are checked before being paired with success metadata.  On failure,
Z22K1 is exactly Z24/Void and the caller-supplied, schema-checked metadata occupies Z22K2. -/
def toEvaluationResult (protocol : ResultProtocol) : Outcome → ZObject
  | .value value =>
      if value.structurallyValid then
        Schema.Core.Z22.result value protocol.successMetadata
      else
        Schema.Core.Z22.result (.reference IDs.z24)
          (protocol.encodeFailureMetadata (.invalidRuntimeValue value))
  | .error error =>
      Schema.Core.Z22.result (.reference IDs.z24)
        (protocol.encodeFailureMetadata (.semantic error))
  | .outOfFuel =>
      Schema.Core.Z22.result (.reference IDs.z24)
        (protocol.encodeFailureMetadata .outOfFuel)

/-- Execute the inner semantics and construct its public Z22 result. -/
def execute (protocol : ResultProtocol) (runtime : Runtime) (fuel : Nat) (expression : Expr) :
    ZObject :=
  toEvaluationResult protocol (eval runtime fuel expression)

/-- A structurally valid runtime value is wrapped without modification. -/
theorem toEvaluationResult_value (protocol : ResultProtocol) (value : ZObject)
    (hvalid : value.structurallyValid = true) :
    toEvaluationResult protocol (.value value) =
      Schema.Core.Z22.result value protocol.successMetadata := by
  simp [toEvaluationResult, hvalid]

/-- Semantic failures put Z24/Void in Z22K1 and their encoded metadata in Z22K2. -/
@[simp]
theorem toEvaluationResult_error (protocol : ResultProtocol) (error : EvalError) :
    toEvaluationResult protocol (.error error) =
      Schema.Core.Z22.result (.reference IDs.z24)
        (protocol.encodeFailureMetadata (.semantic error)) := rfl

/-- Fuel exhaustion is a distinct failure encoded with the same Z24 result convention. -/
@[simp]
theorem toEvaluationResult_outOfFuel (protocol : ResultProtocol) :
    toEvaluationResult protocol .outOfFuel =
      Schema.Core.Z22.result (.reference IDs.z24)
        (protocol.encodeFailureMetadata .outOfFuel) := rfl

/-- Representation-invalid runtime values are also returned as Z22 failure results. -/
theorem toEvaluationResult_invalidValue (protocol : ResultProtocol) (value : ZObject)
    (hinvalid : value.structurallyValid = false) :
    toEvaluationResult protocol (.value value) =
      Schema.Core.Z22.result (.reference IDs.z24)
        (protocol.encodeFailureMetadata (.invalidRuntimeValue value)) := by
  simp [toEvaluationResult, hinvalid]

/-- Every successfully wrapped ordinary value satisfies the pinned literal Z22 schema. -/
theorem evaluationResult_value_schemaValid (protocol : ResultProtocol) (value : ZObject)
    (hvalid : value.structurallyValid = true) :
    Schema.Core.z22LiteralSchema.Valid
      (Schema.Core.Z22.result value protocol.successMetadata) :=
  Schema.Core.z22_result_valid value protocol.successMetadata hvalid
    protocol.successMetadataValid

/-- A failed result has Z24/Void in Z22K1 and schema-checked metadata in Z22K2, and therefore
satisfies the pinned literal Z22 schema. -/
theorem evaluationResult_failure_schemaValid (protocol : ResultProtocol)
    (failure : EvaluationFailure) :
    Schema.Core.z22LiteralSchema.Valid
      (Schema.Core.Z22.result (.reference IDs.z24)
        (protocol.encodeFailureMetadata failure)) :=
  Schema.Core.z22_result_valid (.reference IDs.z24)
    (protocol.encodeFailureMetadata failure) rfl
    (protocol.failureMetadataSchema.structurallyValid
      (protocol.failureMetadataValid failure))

end Wikifunctions.Semantics
