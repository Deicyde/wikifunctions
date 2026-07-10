import Wikifunctions.Model.Decode
import Wikifunctions.Model.Ingest
import Wikifunctions.Model.Schema
import Wikifunctions.Semantics.Decode
import Wikifunctions.Semantics.Elaborate
import Wikifunctions.Semantics.Result
import Wikifunctions.Bridge.CrossRef
import Wikifunctions.Verification.Z12427
import Wikifunctions.Verification.Z13701

/-!
# Public theorem dependency audit

Compiling this module prints the axiom dependencies of the load-bearing public theorems.  The
output is intentionally visible in CI.
-/

#print axioms Wikifunctions.Model.normalize_canonicalize
#print axioms Wikifunctions.Model.canonicalize_normalize
#print axioms Wikifunctions.Model.decodeNormal_toNormal_of_wireSafe
#print axioms Wikifunctions.Model.decodeCanonical_canonicalize_toRaw_of_wireSafe
#print axioms Wikifunctions.Model.ingestNormal_reordered_typed_list
#print axioms Wikifunctions.Model.ingestNormal_malformed_quote_preserved
#print axioms Wikifunctions.Model.ingestNormal_literal_identity_list

#print axioms Wikifunctions.Model.Schema.Core.z7_call_valid
#print axioms Wikifunctions.Model.Schema.Core.z14_composition_valid
#print axioms Wikifunctions.Model.Schema.Core.z14_multiple_bodies_rejected
#print axioms Wikifunctions.Model.Schema.Core.empty_z7_resolver_rejected

#print axioms Wikifunctions.Semantics.FunctionSignature.acceptsArguments_pair_swap
#print axioms Wikifunctions.Semantics.Registry.lookup_wellFormed
#print axioms Wikifunctions.Semantics.eval_reference_resolved
#print axioms Wikifunctions.Semantics.eval_reference_chain
#print axioms Wikifunctions.Semantics.eval_true_identity
#print axioms Wikifunctions.Semantics.evaluateCallee_reference
#print axioms Wikifunctions.Semantics.eval_call_constant_composition
#print axioms Wikifunctions.Semantics.eval_call_lazyIf_true
#print axioms Wikifunctions.Semantics.evalPrimitive_strict_success
#print axioms Wikifunctions.Semantics.evalForeign_success
#print axioms Wikifunctions.Semantics.decode_duplicate_z7_callee_rejected
#print axioms Wikifunctions.Semantics.elaborateImplementation_builtin
#print axioms Wikifunctions.Semantics.elaboratePersistentImplementation_builtin
#print axioms Wikifunctions.Semantics.elaborateImplementation_invalid_builtin_rejected
#print axioms Wikifunctions.Semantics.evaluationResult_value_schemaValid
#print axioms Wikifunctions.Semantics.evaluationResult_failure_schemaValid
#print axioms Wikifunctions.Semantics.toEvaluationResult_invalidValue

#print axioms Wikifunctions.Bridge.Codec.encode_injective
#print axioms Wikifunctions.Bridge.Natural.decode_encode
#print axioms Wikifunctions.Bridge.Natural.encode_schemaValid
#print axioms Wikifunctions.Bridge.Boolean.decode_encode
#print axioms Wikifunctions.Bridge.Boolean.encode_schemaValid
#print axioms Wikifunctions.Bridge.z12427_spec_eq_true_iff
#print axioms Wikifunctions.Bridge.z12427_oracle_encode_eq_true_iff

#print axioms Wikifunctions.Verification.ConformsWithFuel.conforms
#print axioms Wikifunctions.Verification.Z12427.eval_eq_true_iff_of_conformsWithFuel
#print axioms Wikifunctions.Verification.Z13701.liveBody_schemaValid
#print axioms Wikifunctions.Verification.Z13701.decode_liveBody
#print axioms Wikifunctions.Verification.Z13701.elaborate_liveImplementation
#print axioms Wikifunctions.Verification.Z13701.eval_contract
#print axioms Wikifunctions.Verification.Z13701.conforms
#print axioms Wikifunctions.Verification.Z13701.eval_eq_true_iff
