import Wikifunctions.Model.Schema
import Wikifunctions.Semantics.Eval

/-!
# Decoding semantic composition syntax

This module is the small boundary between schema-shaped semantic `ZObject`s and the evaluator's
`Expr` syntax.  It deliberately does not decode JSON; wire decoding belongs to
`Wikifunctions.Model.Decode`.

Two object types are reserved as expression forms:

* `Z18` is an argument reference with exactly one `Z18K1` global-key string;
* `Z7` is a call with one expression-valued `Z7K1` callee and dynamically keyed expression
  arguments.

An object carrying either reserved type is rejected when malformed.  In particular it never
falls through to the literal case.  Quotes are opaque: their payload is neither inspected nor
recursively decoded.  Other structurally valid semantic values are literals.
-/

namespace Wikifunctions.Semantics

open Wikifunctions.Model

/-- Failures at the semantic-object/expression boundary. -/
inductive DecodeError where
  | outOfFuel
  | structurallyInvalid
  | malformedArgument
  | invalidArgumentKey (raw : String)
  | malformedCall
deriving Repr, DecidableEq

/-- Decode the fields of a well-shaped Z18 argument reference. -/
def decodeArgumentFields : List (Key × ZObject) → Except DecodeError Expr
  | [(fieldKey, .string raw)] =>
      if fieldKey == Keys.z18k1 && Schema.isGlobalKey raw then
        match Key.parse raw with
        | some key => .ok (.argument key)
        | none => .error (.invalidArgumentKey raw)
      else
        .error .malformedArgument
  | _ => .error .malformedArgument

/-- Decode dynamically keyed Z7 arguments with the supplied recursive decoder. -/
def decodeDynamicArguments (run : ZObject → Except DecodeError Expr) :
    List (Key × ZObject) → Except DecodeError Arguments
  | [] => .ok []
  | (key, value) :: fields => do
      let expression ← run value
      let arguments ← decodeDynamicArguments run fields
      pure ((key, expression) :: arguments)

/-- Remove the unique Z7 callee field while retaining dynamic argument order. -/
def dynamicFields (fields : List (Key × ZObject)) : List (Key × ZObject) :=
  fields.filter (fun field => field.1 != Keys.z7k1)

/-- Decode semantic composition syntax with an explicit expression-depth bound.

Fuel bounds recursive descent through calls.  Literals and opaque quotes consume one unit but do
not traverse their contents.  Structural validation rejects duplicate fields before the special
forms are inspected. -/
def decode : Nat → ZObject → Except DecodeError Expr
  | 0, _ => .error .outOfFuel
  | _ + 1, .quote payload => .ok (.quote payload)
  | fuel + 1, value =>
      if value.structurallyValid then
        match value with
        | .object (.reference typeId) fields =>
            if typeId = IDs.z18 then
              decodeArgumentFields fields
            else if typeId = IDs.z7 then
              match Schema.T.field? fields Keys.z7k1 with
              | none => .error .malformedCall
              | some callee => do
                  let decodedCallee ← decode fuel callee
                  let arguments ← decodeDynamicArguments (decode fuel) (dynamicFields fields)
                  pure (.call decodedCallee arguments)
            else
              .ok (.literal value)
        | _ => .ok (.literal value)
      else
        .error .structurallyInvalid

/-! ## Basic decoding laws -/

@[simp]
theorem decode_zero (value : ZObject) : decode 0 value = .error .outOfFuel := rfl

@[simp]
theorem decode_string (fuel : Nat) (value : String) :
    decode (fuel + 1) (.string value) = .ok (.literal (.string value)) := rfl

@[simp]
theorem decode_reference (fuel : Nat) (zid : ZID) :
    decode (fuel + 1) (.reference zid) = .ok (.literal (.reference zid)) := rfl

/-- Quote opacity holds without any condition on, or traversal of, the payload. -/
@[simp]
theorem decode_quote (fuel : Nat) (payload : Raw) :
    decode (fuel + 1) (.quote payload) = .ok (.quote payload) := rfl

/-- The complete keyed Z18 representation decodes to an evaluator argument. -/
theorem decode_z18_argument_of_parse (fuel : Nat) (raw : String) (key : Key)
    (hglobal : Schema.isGlobalKey raw = true) (hparse : Key.parse raw = some key) :
    decode (fuel + 1)
        (.object (.reference IDs.z18) [(Keys.z18k1, .string raw)]) =
      .ok (.argument key) := by
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup, decodeArgumentFields, hglobal, hparse]

/-- A Z7 callee is decoded as an expression, rather than assumed to be a direct reference. -/
theorem decode_z7_no_arguments (fuel : Nat) (callee : ZObject) (decodedCallee : Expr)
    (hcalleeValid : callee.structurallyValid = true)
    (hcallee : decode (fuel + 1) callee = .ok decodedCallee) :
    decode (fuel + 2)
        (.object (.reference IDs.z7) [(Keys.z7k1, callee)]) =
      .ok (.call decodedCallee []) := by
  have htype : IDs.z7 ≠ IDs.z18 := by decide
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup, Schema.T.field?, dynamicFields, decodeDynamicArguments,
    hcalleeValid, hcallee, htype]
  rfl

/-- Dynamic Z7 argument keys and argument expressions are preserved. -/
theorem decode_z7_one_argument (fuel : Nat) (callee value : ZObject)
    (decodedCallee decodedValue : Expr) (key : Key)
    (hkey : key ≠ Keys.z7k1)
    (hnotTypeKey : key ≠ Keys.z1k1)
    (hcalleeValid : callee.structurallyValid = true)
    (hvalueValid : value.structurallyValid = true)
    (hcallee : decode (fuel + 1) callee = .ok decodedCallee)
    (hvalue : decode (fuel + 1) value = .ok decodedValue) :
    decode (fuel + 2)
        (.object (.reference IDs.z7)
          [(Keys.z7k1, callee), (key, value)]) =
      .ok (.call decodedCallee [(key, decodedValue)]) := by
  have htype : IDs.z7 ≠ IDs.z18 := by decide
  have hcalleeKey : Keys.z7k1 ≠ key := Ne.symm hkey
  have htypeKey : Keys.z1k1 ≠ key := Ne.symm hnotTypeKey
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup, Schema.T.field?, dynamicFields, decodeDynamicArguments,
    hkey, hcalleeKey, htypeKey, hcalleeValid, hvalueValid, hcallee, hvalue, htype]
  rfl

/-- A missing Z18 payload is a malformed special form, not a literal object. -/
@[simp]
theorem decode_empty_z18_rejected (fuel : Nat) :
    decode (fuel + 1) (.object (.reference IDs.z18) []) =
      .error .malformedArgument := by
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup, decodeArgumentFields]

/-- A missing Z7 callee is a malformed special form, not a literal object. -/
@[simp]
theorem decode_empty_z7_rejected (fuel : Nat) :
    decode (fuel + 1) (.object (.reference IDs.z7) []) =
      .error .malformedCall := by
  have htype : IDs.z7 ≠ IDs.z18 := by decide
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup, Schema.T.field?, htype]

/-- Duplicate special-form fields are rejected by structural validation before dispatch. -/
@[simp]
theorem decode_duplicate_z7_callee_rejected (fuel : Nat) (callee : ZObject) :
    decode (fuel + 1)
        (.object (.reference IDs.z7)
          [(Keys.z7k1, callee), (Keys.z7k1, callee)]) =
      .error .structurallyInvalid := by
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup]

/-- Duplicate Z18 payload fields are rejected before their key strings are interpreted. -/
@[simp]
theorem decode_duplicate_z18_payload_rejected (fuel : Nat) (raw : String) :
    decode (fuel + 1)
        (.object (.reference IDs.z18)
          [(Keys.z18k1, .string raw), (Keys.z18k1, .string raw)]) =
      .error .structurallyInvalid := by
  simp [decode, ZObject.structurallyValid, ZObject.structurallyValidFields,
    ZObject.keysNoDup]

end Wikifunctions.Semantics
