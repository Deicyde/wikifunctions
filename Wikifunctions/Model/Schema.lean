import Wikifunctions.Model.ZObject
import Std.Data.String.ToNat

/-!
# Executable structural schemas

This module contains the small, auditable schema language used by the semantic model.  It is
not an encoding of arbitrary JSON Schema.  Instead, it records the fragment used by normal-form
Wikifunctions objects: refined terminals, typed lists, required and optional fields, exclusive
field groups, and explicit policies for additional keys.

The schemas below are transcribed from the normal schemata at function-schemata commit
`40db6bc971df332a562de6080e6cb418ef813437`.  `Z13518` is transcribed from live revision
`282417`; its decimal rule is the canonical codec invariant layered over its Z6 field.
-/

namespace Wikifunctions.Model

open ZObject

namespace Schema

namespace Source

/-- Immutable upstream function-schemata snapshot used by the built-in schemas. -/
def functionSchemataCommit : String :=
  "40db6bc971df332a562de6080e6cb418ef813437"

/-- Wikifunctions revision of the Z13518 type used by this model. -/
def z13518Revision : Nat := 282417

end Source

/-! ## Refinements -/

/-- A global key has the form `Z<n>K<m>`, with both numerals positive and canonical. -/
def isGlobalKey (s : String) : Bool :=
  match s.toList with
  | 'Z' :: digit :: rest => digit.isDigit && digit != '0' && globalKeyTail rest
  | _ => false

/-- A local key has the form `K<n>`, with a positive canonical numeral. -/
def isLocalKey (s : String) : Bool :=
  match s.toList with
  | 'K' :: digits => positiveDigits digits
  | _ => false

/-- Decimal syntax for a natural number: either `0`, or a positive numeral without leading 0. -/
def isNaturalDecimal (s : String) : Bool :=
  match s.toNat? with
  | some value => toString value == s
  | none => false

@[simp]
theorem isNaturalDecimal_toString (value : Nat) :
    isNaturalDecimal (toString value) = true := by
  simp [isNaturalDecimal, Nat.toNat?_repr]

theorem isNaturalDecimal_eq_true_iff (value : String) :
    isNaturalDecimal value = true ↔ ∃ number : Nat, toString number = value := by
  unfold isNaturalDecimal
  cases hparse : value.toNat? with
  | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨number, rfl⟩
      simp [Nat.toNat?_repr] at hparse
  | some number =>
      simp only [beq_iff_eq]
      constructor
      · intro h
        exact ⟨number, h⟩
      · rintro ⟨candidate, hcandidate⟩
        have hcandidateParse : value.toNat? = some candidate := by
          rw [← hcandidate]
          exact Nat.toNat?_repr candidate
        have hcandidates : candidate = number :=
          Option.some.inj (hcandidateParse.symm.trans hparse)
        simpa [hcandidates] using hcandidate

/-- Executable refinements for Z6/String values. -/
inductive StringRule where
  | any
  | nonempty
  | zid
  | key
  | globalKey
  | naturalDecimal
  | oneOf (values : List String)
deriving Repr, DecidableEq

namespace StringRule

/-- Test a string against a refinement. -/
def accepts : StringRule → String → Bool
  | .any, _ => true
  | .nonempty, value => !value.isEmpty
  | .zid, value => isZID value
  | .key, value => isKey value
  | .globalKey, value => isGlobalKey value
  | .naturalDecimal, value => isNaturalDecimal value
  | .oneOf values, value => values.contains value

end StringRule

/-- Executable refinements for Z9/Reference values. -/
inductive ReferenceRule where
  | any
  | exact (zid : ZID)
  | oneOf (zids : List ZID)
deriving Repr, DecidableEq

namespace ReferenceRule

/-- Test a reference against a refinement. -/
def accepts : ReferenceRule → ZID → Bool
  | .any, _ => true
  | .exact expected, actual => actual == expected
  | .oneOf expected, actual => expected.contains actual

end ReferenceRule

/-- Auditable key classes used by an additional-key policy. -/
inductive KeyClass where
  | local
  | global
  | zid
deriving Repr, DecidableEq

namespace KeyClass

/-- Test a key against a syntactic key class. -/
def accepts : KeyClass → Key → Bool
  | .local, key => isLocalKey key.raw
  | .global, key => isGlobalKey key.raw
  | .zid, key => isZID key.raw

end KeyClass

/-- Policy for object fields not named by a required or optional rule. -/
inductive ExtraKeys where
  | reject
  | allow
  | matching (classes : List KeyClass)
deriving Repr, DecidableEq

/-- The four resolver unions named by function-schemata. -/
inductive ResolverRule where
  | all
  | withoutReference
  | withoutCall
  | argumentOnly
deriving Repr, DecidableEq

namespace ResolverRule

def allowsReference : ResolverRule → Bool
  | .all | .withoutCall => true
  | .withoutReference | .argumentOnly => false

def allowsCall : ResolverRule → Bool
  | .all | .withoutReference => true
  | .withoutCall | .argumentOnly => false

end ResolverRule

/-! ## Schema language -/

/-- The structural schema fragment needed by normal-form semantic ZObjects. -/
inductive T where
  | any
  | string (rule : StringRule)
  | reference (rule : ReferenceRule)
  | object
      (typeId : ZID)
      (required : List (Key × T))
      (optional : List (Key × T))
      (exactlyOne : List (List Key))
      (extraKeys : ExtraKeys)
  | list (elementType : T) (element : T)
  | anyOf (alternatives : List T)
  | resolver (rule : ResolverRule)
deriving Repr

namespace T

/-- Keys named directly by an object schema. -/
def declaredKeys : List (Key × T) → List (Key × T) → List Key
  | required, optional => (required ++ optional).map (fun field => field.1)

/-- Whether a key has a corresponding field rule. -/
def isDeclared (required optional : List (Key × T)) (key : Key) : Bool :=
  (declaredKeys required optional).contains key

/-- Look up a semantic object's data field. -/
def field? (fields : List (Key × ZObject)) (key : Key) : Option ZObject :=
  (fields.find? (fun field => field.1 == key)).map (fun field => field.2)

/-- Count the keys from a group that occur in an object. -/
def presentCount (fields : List (Key × ZObject)) (keys : List Key) : Nat :=
  (keys.filter (fun key => (field? fields key).isSome)).length

/-- Test the policy for one additional field. -/
def extraKeyAllowed (policy : ExtraKeys) (key : Key) : Bool :=
  match policy with
  | .reject => false
  | .allow => true
  | .matching classes => classes.any (fun keyClass => keyClass.accepts key)

/-- Check that exclusive groups are nonempty, unique, and refer to declared fields. -/
def exclusiveGroupsValid (required optional : List (Key × T))
    (groups : List (List Key)) : Bool :=
  groups.all (fun group =>
    !group.isEmpty &&
      keysNoDup group &&
      group.all (isDeclared required optional))

/-- Recursively validate the resolver fragment (Z9, Z7, and Z18) with bounded depth. -/
def resolverAcceptsAux : ResolverRule → Nat → ZObject → Bool
  | _, 0, _ => false
  | rule, fuel + 1, z =>
      z.structurallyValid &&
        match z with
        | .reference _ => rule.allowsReference
        | .object (.reference typeId) fields =>
            if typeId == IDs.z7 then
              rule.allowsCall &&
                match field? fields Keys.z7k1 with
                | some function =>
                    resolverAcceptsAux .all fuel function &&
                      fields.all (fun field =>
                        field.1 == Keys.z7k1 ||
                          isLocalKey field.1.raw ||
                          isGlobalKey field.1.raw ||
                          isZID field.1.raw)
                | none => false
            else if typeId == IDs.z18 then
              match field? fields Keys.z18k1 with
              | some (.string key) =>
                  isGlobalKey key && fields.all (fun field => field.1 == Keys.z18k1)
              | _ => false
            else false
        | _ => false

/-- Validate a semantic value with explicit recursion fuel.  Structural validity is checked. -/
def accepts : T → Nat → ZObject → Bool
  | _, 0, _ => false
  | .any, _ + 1, z => z.structurallyValid
  | .string rule, _ + 1, z =>
      z.structurallyValid &&
        match z with
        | .string value => rule.accepts value
        | _ => false
  | .reference rule, _ + 1, z =>
      z.structurallyValid &&
        match z with
        | .reference zid => rule.accepts zid
        | _ => false
  | .object typeId required optional exactlyOne extraKeys, fuel + 1, z =>
      z.structurallyValid &&
        match z with
        | .object (.reference actualType) fields =>
            actualType == typeId &&
              keysNoDup (declaredKeys required optional) &&
              exclusiveGroupsValid required optional exactlyOne &&
              required.all (fun field =>
                match field? fields field.1 with
                | some value => accepts field.2 fuel value
                | none => false) &&
              optional.all (fun field =>
                match field? fields field.1 with
                | some value => accepts field.2 fuel value
                | none => true) &&
              exactlyOne.all (fun group => presentCount fields group == 1) &&
              fields.all (fun field =>
                isDeclared required optional field.1 || extraKeyAllowed extraKeys field.1)
        | _ => false
  | .list elementType element, fuel + 1, z =>
      z.structurallyValid &&
        match z with
        | .list actualType elements =>
            accepts elementType fuel actualType &&
              elements.all (accepts element fuel)
        | _ => false
  | .anyOf alternatives, fuel + 1, z =>
      z.structurallyValid &&
        alternatives.any (fun alternative => accepts alternative fuel z)
  | .resolver rule, fuel + 1, z => resolverAcceptsAux rule (fuel + 1) z

/-- Validation at a stated resource bound. -/
def ValidAt (schema : T) (fuel : Nat) (z : ZObject) : Prop :=
  schema.accepts fuel z = true

/-- A value is valid when the executable validator accepts it with some finite fuel. -/
def Valid (schema : T) (z : ZObject) : Prop :=
  ∃ fuel, schema.ValidAt fuel z

instance (schema : T) (fuel : Nat) (z : ZObject) : Decidable (ValidAt schema fuel z) := by
  unfold ValidAt
  infer_instance

/-- Every successful schema check includes representation-level structural validity. -/
theorem structurallyValid_of_accepts {schema : T} {fuel : Nat} {value : ZObject}
    (h : schema.accepts fuel value = true) : value.structurallyValid = true := by
  cases fuel with
  | zero => simp [accepts] at h
  | succ fuel =>
      cases schema <;> simp_all [accepts, resolverAcceptsAux]

end T

/-- An executable schema together with the explicit fuel bound used at a typed boundary.

Keeping the bound in the data makes validation reproducible: callers never rely on an implicit
search for the existential witness in `T.Valid`. -/
structure Checked where
  schema : T
  fuel : Nat
deriving Repr

namespace Checked

/-- Execute a checked schema at its declared bound. -/
def accepts (checked : Checked) (value : ZObject) : Bool :=
  checked.schema.accepts checked.fuel value

/-- Proposition-valued checked-schema validity. -/
def Valid (checked : Checked) (value : ZObject) : Prop :=
  checked.accepts value = true

instance (checked : Checked) (value : ZObject) : Decidable (checked.Valid value) := by
  unfold Valid
  infer_instance

/-- Checked-schema validity entails structural validity. -/
theorem structurallyValid {checked : Checked} {value : ZObject}
    (h : checked.Valid value) : value.StructurallyValid := by
  exact T.structurallyValid_of_accepts h

end Checked

/-! ## Core normal-form schemas and smart constructors -/

namespace Core

open T

@[simp] private theorem z1k1_ne_z7k1 : Keys.z1k1 ≠ Keys.z7k1 := by decide
@[simp] private theorem z1k1_ne_z18k1 : Keys.z1k1 ≠ Keys.z18k1 := by decide
@[simp] private theorem z1k1_ne_z14k1 : Keys.z1k1 ≠ Keys.z14k1 := by decide
@[simp] private theorem z1k1_ne_z14k2 : Keys.z1k1 ≠ Keys.z14k2 := by decide
@[simp] private theorem z1k1_ne_z14k3 : Keys.z1k1 ≠ Keys.z14k3 := by decide
@[simp] private theorem z1k1_ne_z14k4 : Keys.z1k1 ≠ Keys.z14k4 := by decide
@[simp] private theorem z1k1_ne_z22k1 : Keys.z1k1 ≠ Keys.z22k1 := by decide
@[simp] private theorem z1k1_ne_z22k2 : Keys.z1k1 ≠ Keys.z22k2 := by decide
@[simp] private theorem z1k1_ne_z13518k1 : Keys.z1k1 ≠ Keys.z13518k1 := by decide
@[simp] private theorem z14k1_ne_z14k2 : Keys.z14k1 ≠ Keys.z14k2 := by decide
@[simp] private theorem z14k1_ne_z14k3 : Keys.z14k1 ≠ Keys.z14k3 := by decide
@[simp] private theorem z14k1_ne_z14k4 : Keys.z14k1 ≠ Keys.z14k4 := by decide
@[simp] private theorem z14k2_ne_z14k3 : Keys.z14k2 ≠ Keys.z14k3 := by decide
@[simp] private theorem z14k2_ne_z14k4 : Keys.z14k2 ≠ Keys.z14k4 := by decide
@[simp] private theorem z14k3_ne_z14k4 : Keys.z14k3 ≠ Keys.z14k4 := by decide
@[simp] private theorem z14k4_ne_z14k2 : Keys.z14k4 ≠ Keys.z14k2 := by decide
@[simp] private theorem z14k4_ne_z14k3 : Keys.z14k4 ≠ Keys.z14k3 := by decide
@[simp] private theorem z22k1_ne_z22k2 : Keys.z22k1 ≠ Keys.z22k2 := by decide

/-- A recursively checked Z9, Z7, or Z18 resolver expression. -/
def resolverSchema : T := .resolver .all

/-- A resolver excluding root references, used by non-root object types such as Z16. -/
def resolverWithoutReferenceSchema : T := .resolver .withoutReference

/-- A resolver excluding calls, used to break the recursive Z7 schema dependency. -/
def resolverWithoutCallSchema : T := .resolver .withoutCall

/-- Literal normal-form Z16/Code. -/
def z16LiteralSchema : T :=
  .object IDs.z16
    [(Keys.z16k1, resolverSchema), (Keys.z16k2, .string .any)] [] [] .reject

/-- Normal Z16, including the resolver branch that excludes root references. -/
def z16Schema : T := .anyOf [z16LiteralSchema, resolverWithoutReferenceSchema]

/-- Literal Z7/Function call, including dynamically named local and global arguments. -/
def z7LiteralSchema : T :=
  .object IDs.z7 [(Keys.z7k1, resolverSchema)] [] []
    (.matching [.local, .global, .zid])

/-- Normal Z7, including the non-call resolver branch. -/
def z7Schema : T := .anyOf [z7LiteralSchema, resolverWithoutCallSchema]

/-- Normal-form Z18/Argument reference. -/
def z18Schema : T :=
  .object IDs.z18 [(Keys.z18k1, .string .globalKey)] [] [] .reject

/-- Literal Z14/Implementation: exactly one composition, code, or builtin body. -/
def z14LiteralSchema : T :=
  .object IDs.z14
    [(Keys.z14k1, resolverSchema)]
    [(Keys.z14k2, .any),
      (Keys.z14k3, z16Schema),
      (Keys.z14k4, .string .zid)]
    [[Keys.z14k2, Keys.z14k3, Keys.z14k4]] .reject

/-- Normal Z14, including its unrestricted resolver branch. -/
def z14Schema : T := .anyOf [z14LiteralSchema, resolverSchema]

/-- Literal Z22/Evaluation result.  Both result and metadata are required ZObjects. -/
def z22LiteralSchema : T :=
  .object IDs.z22 [(Keys.z22k1, .any), (Keys.z22k2, .any)] [] [] .reject

/-- Normal Z22, including its unrestricted resolver branch. -/
def z22Schema : T := .anyOf [z22LiteralSchema, resolverSchema]

/-- Literal Z40/Boolean.  The identity key is optional in the pinned structural schema. -/
def z40LiteralSchema : T :=
  .object IDs.z40 []
    [(Keys.z40k1, .reference (.oneOf [IDs.z41, IDs.z42]))] [] .reject

/-- Normal Z40, including its unrestricted resolver branch. -/
def z40Schema : T := .anyOf [z40LiteralSchema, resolverSchema]

/-- Live Z13518/Natural number, represented by a canonical nonnegative decimal string. -/
def z13518Schema : T :=
  .object IDs.z13518 [(Keys.z13518k1, .string .naturalDecimal)] [] [] .reject

/-- A typed list of references, included as the core refined-list schema pattern. -/
def referenceListSchema (elementType : ZID) : T :=
  .list (.reference (.exact elementType)) (.reference .any)

namespace Z7

/-- Construct a function call; `z7_call_valid` states its dynamic-argument obligations. -/
def call (functionId : ZID) (arguments : List (Key × ZObject)) : ZObject :=
  .object (.reference IDs.z7) ((Keys.z7k1, .reference functionId) :: arguments)

/-- A witness for the bare-ZID dynamic-key branch in the pinned Z7 schema. -/
def exampleBareZidKey : Key := ⟨"Z123", by decide⟩

end Z7

namespace Z16

/-- Construct a code value from a language reference and source text. -/
def code (language : ZID) (source : String) : ZObject :=
  .object (.reference IDs.z16)
    [(Keys.z16k1, .reference language), (Keys.z16k2, .string source)]

end Z16

/-- A global argument key accepted by Z18. -/
structure ArgumentKey where
  raw : String
  valid : isGlobalKey raw = true
deriving Repr, DecidableEq

namespace Z18

/-- Construct an argument reference from a validated global argument key. -/
def argument (key : ArgumentKey) : ZObject :=
  .object (.reference IDs.z18) [(Keys.z18k1, .string key.raw)]

end Z18

namespace Z14

/-- Construct a composition implementation. -/
def composition (functionId : ZID) (body : ZObject) : ZObject :=
  .object (.reference IDs.z14)
    [(Keys.z14k1, .reference functionId), (Keys.z14k2, body)]

/-- Construct a code implementation. -/
def code (functionId : ZID) (implementation : ZObject) : ZObject :=
  .object (.reference IDs.z14)
    [(Keys.z14k1, .reference functionId), (Keys.z14k3, implementation)]

/-- Construct a builtin implementation from its persistent builtin ZID. -/
def builtin (functionId builtinId : ZID) : ZObject :=
  .object (.reference IDs.z14)
    [(Keys.z14k1, .reference functionId), (Keys.z14k4, .string builtinId.raw)]

end Z14

namespace Z22

/-- Construct an evaluation result from its value and metadata. -/
def result (value metadata : ZObject) : ZObject :=
  .object (.reference IDs.z22)
    [(Keys.z22k1, value), (Keys.z22k2, metadata)]

end Z22

namespace Z40

/-- The normal-form true Boolean. -/
def trueValue : ZObject :=
  .object (.reference IDs.z40) [(Keys.z40k1, .reference IDs.z41)]

/-- The normal-form false Boolean. -/
def falseValue : ZObject :=
  .object (.reference IDs.z40) [(Keys.z40k1, .reference IDs.z42)]

end Z40

/-- A decimal natural-number literal accepted by Z13518. -/
structure NaturalLiteral where
  raw : String
  valid : isNaturalDecimal raw = true
deriving Repr, DecidableEq

namespace Z13518

/-- Construct a live natural-number value from a validated decimal literal. -/
def natural (value : NaturalLiteral) : ZObject :=
  .object (.reference IDs.z13518) [(Keys.z13518k1, .string value.raw)]

end Z13518

/-! ## Constructor correctness -/

theorem z7_call_valid (functionId : ZID) (arguments : List (Key × ZObject))
    (unique : keysNoDup (Keys.z7k1 :: arguments.map (fun field => field.1)) = true)
    (noTypeKey : ∀ value, (Keys.z1k1, value) ∉ arguments)
    (valuesValid : structurallyValidFields arguments = true)
    (argumentKeys : ∀ key value, (key, value) ∈ arguments →
      key = Keys.z7k1 ∨ isLocalKey key.raw = true ∨ isGlobalKey key.raw = true ∨
        isZID key.raw = true) :
    z7LiteralSchema.Valid (Z7.call functionId arguments) := by
  refine ⟨8, ?_⟩
  simp [T.ValidAt, z7LiteralSchema, Z7.call, resolverSchema, T.accepts, unique, noTypeKey,
    valuesValid, ZObject.structurallyValid, ZObject.keysNoDup,
    ZObject.structurallyValidFields, T.declaredKeys, T.exclusiveGroupsValid,
    T.field?, T.isDeclared, T.extraKeyAllowed, KeyClass.accepts,
    T.resolverAcceptsAux, ResolverRule.allowsReference]
  exact argumentKeys

/-- The upstream Z7 pattern's bare-ZID dynamic argument-key alternative is represented. -/
theorem z7_bare_zid_argument_valid (functionId : ZID) :
    z7LiteralSchema.Valid
      (Z7.call functionId [(Z7.exampleBareZidKey, .reference functionId)]) := by
  apply z7_call_valid
  · have hkey : Keys.z7k1 ≠ Z7.exampleBareZidKey := by decide
    simpa [ZObject.keysNoDup] using hkey
  · intro value h
    have hp : (Keys.z1k1, value) =
        (Z7.exampleBareZidKey, ZObject.reference functionId) := by
      simpa only [List.mem_singleton] using h
    exact (show Keys.z1k1 ≠ Z7.exampleBareZidKey by decide) (congrArg Prod.fst hp)
  · rfl
  · intro key value h
    simp only [List.mem_singleton] at h
    cases h
    exact Or.inr (Or.inr (Or.inr (by decide)))

theorem z16_code_valid (language : ZID) (source : String) :
    z16LiteralSchema.Valid (Z16.code language source) := by
  exact ⟨8, rfl⟩

theorem z18_argument_valid (key : ArgumentKey) :
    z18Schema.Valid (Z18.argument key) := by
  refine ⟨8, ?_⟩
  cases key with
  | mk raw valid =>
      simp [T.ValidAt, z18Schema, Z18.argument, T.accepts, valid,
        ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup,
        T.declaredKeys, T.exclusiveGroupsValid, T.field?, T.isDeclared,
        T.extraKeyAllowed, StringRule.accepts]

theorem z14_composition_valid (functionId : ZID) (body : ZObject)
    (bodyValid : body.structurallyValid = true) :
    z14LiteralSchema.Valid (Z14.composition functionId body) := by
  refine ⟨12, ?_⟩
  simp [T.ValidAt, z14LiteralSchema, Z14.composition, resolverSchema, T.accepts,
    bodyValid, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup, T.declaredKeys, T.exclusiveGroupsValid, T.field?,
    T.presentCount, T.isDeclared, T.extraKeyAllowed, T.resolverAcceptsAux,
    ResolverRule.allowsReference]

theorem z14_code_valid (functionId language : ZID) (source : String) :
    z14LiteralSchema.Valid (Z14.code functionId (Z16.code language source)) := by
  exact ⟨12, rfl⟩

theorem z14_builtin_valid (functionId builtinId : ZID) :
    z14LiteralSchema.Valid (Z14.builtin functionId builtinId) := by
  refine ⟨8, ?_⟩
  simp [T.ValidAt, z14LiteralSchema, Z14.builtin, resolverSchema, T.accepts,
    ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup,
    T.declaredKeys, T.exclusiveGroupsValid, T.field?, T.presentCount, T.isDeclared,
    T.extraKeyAllowed, StringRule.accepts, builtinId.valid,
    T.resolverAcceptsAux, ResolverRule.allowsReference]

theorem z22_result_valid (value metadata : ZObject)
    (valueValid : value.structurallyValid = true)
    (metadataValid : metadata.structurallyValid = true) :
    z22LiteralSchema.Valid (Z22.result value metadata) := by
  refine ⟨8, ?_⟩
  simp [T.ValidAt, z22LiteralSchema, Z22.result, T.accepts, valueValid, metadataValid,
    ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup,
    T.declaredKeys, T.exclusiveGroupsValid, T.field?, T.isDeclared,
    T.extraKeyAllowed]

theorem z40_true_valid : z40LiteralSchema.Valid Z40.trueValue := by
  exact ⟨4, rfl⟩

theorem z40_false_valid : z40LiteralSchema.Valid Z40.falseValue := by
  exact ⟨4, rfl⟩

theorem z13518_natural_valid (value : NaturalLiteral) :
    z13518Schema.Valid (Z13518.natural value) := by
  refine ⟨4, ?_⟩
  cases value with
  | mk raw valid =>
      simp [T.ValidAt, z13518Schema, Z13518.natural, T.accepts, valid,
        ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup,
        T.declaredKeys, T.exclusiveGroupsValid, T.field?, T.isDeclared,
        T.extraKeyAllowed, StringRule.accepts]

theorem empty_reference_list_valid (elementType : ZID) :
    (referenceListSchema elementType).Valid (.list (.reference elementType) []) := by
  refine ⟨4, ?_⟩
  simp [T.ValidAt, referenceListSchema, T.accepts, ZObject.structurallyValid,
    ZObject.structurallyValidList, ReferenceRule.accepts]

/-- Structural uniqueness rejects an otherwise well-shaped object with a duplicate key. -/
theorem z22_duplicate_result_rejected (value metadata : ZObject) (fuel : Nat) :
    z22LiteralSchema.accepts fuel
      (.object (.reference IDs.z22)
        [(Keys.z22k1, value), (Keys.z22k1, value), (Keys.z22k2, metadata)]) = false := by
  cases fuel <;> rfl

/-- The exclusive body group rejects a Z14 carrying both composition and builtin bodies. -/
theorem z14_multiple_bodies_rejected (functionId : ZID) (fuel : Nat) :
    z14LiteralSchema.accepts fuel
      (.object (.reference IDs.z14)
        [(Keys.z14k1, .reference functionId),
          (Keys.z14k2, .string "body"),
          (Keys.z14k4, .string "builtin")]) = false := by
  cases fuel with
  | zero => rfl
  | succ fuel => cases fuel <;> rfl

/-- A type tag alone is not enough to make a valid function-call resolver. -/
theorem empty_z7_resolver_rejected (fuel : Nat) :
    resolverSchema.accepts fuel (.object (.reference IDs.z7) []) = false := by
  cases fuel <;> rfl

/-- An argument resolver must contain its single, refined global-key field. -/
theorem empty_z18_resolver_rejected (fuel : Nat) :
    resolverSchema.accepts fuel (.object (.reference IDs.z18) []) = false := by
  cases fuel <;> rfl

end Core
end Schema
end Wikifunctions.Model
