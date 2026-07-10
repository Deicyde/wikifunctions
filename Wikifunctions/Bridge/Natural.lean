import Wikifunctions.Bridge.Codec
import Std.Data.String.ToNat

/-!
# Codec for Wikifunctions natural numbers

The deployed Z13518 type stores a natural number in field Z13518K1 as a Z6 string containing its
base-10 representation.  The decoder below intentionally accepts only the canonical decimal
spelling produced by Lean's natural-number printer; in particular, leading-zero spellings are
not silently normalized.  The shape was checked against Wikifunctions Z13518 revision 282417.
-/

namespace Wikifunctions.Bridge

open Model

namespace Natural

/-- The deployed semantic Z13518 representation of a natural number. -/
def encode (value : Nat) : ZObject :=
  .object (.reference IDs.z13518) [(Keys.z13518k1, .string (toString value))]

/-- Parse a canonical nonnegative base-10 numeral. -/
def decodeDecimal (digits : String) : Option Nat := do
  let value ← digits.toNat?
  if toString value = digits then some value else none

/-- Decode exactly the deployed Z13518 object shape produced by `encode`. -/
def decode : ZObject → Option Nat
  | .object (.reference typeId) [(key, .string digits)] =>
      if typeId = IDs.z13518 ∧ key = Keys.z13518k1 then decodeDecimal digits else none
  | _ => none

@[simp]
theorem decodeDecimal_toString (value : Nat) : decodeDecimal (toString value) = some value := by
  simp [decodeDecimal, Nat.toNat?_repr]

theorem toString_eq_of_decodeDecimal_eq_some {digits : String} {value : Nat}
    (h : decodeDecimal digits = some value) : toString value = digits := by
  unfold decodeDecimal at h
  cases hdigits : digits.toNat? with
  | none =>
      rw [hdigits] at h
      contradiction
  | some parsed =>
      rw [hdigits] at h
      change (if toString parsed = digits then some parsed else none) = some value at h
      by_cases hcanonical : toString parsed = digits
      · rw [if_pos hcanonical] at h
        simpa only [Option.some.inj h] using hcanonical
      · rw [if_neg hcanonical] at h
        contradiction

@[simp]
theorem decode_encode (value : Nat) : decode (encode value) = some value := by
  simpa only [decode, encode, and_self, if_true] using decodeDecimal_toString value

theorem encode_of_decode_eq_some {object : ZObject} {value : Nat}
    (h : decode object = some value) : encode value = object := by
  cases object with
  | string string => simp [decode] at h
  | reference zid => simp [decode] at h
  | list elementType items => simp [decode] at h
  | quote payload => simp [decode] at h
  | object type fields =>
      cases type with
      | string string => simp [decode] at h
      | object nestedType nestedFields => simp [decode] at h
      | list elementType items => simp [decode] at h
      | quote payload => simp [decode] at h
      | reference typeId =>
          cases fields with
          | nil => simp [decode] at h
          | cons field rest =>
              cases rest with
              | cons next remaining => simp [decode] at h
              | nil =>
                  rcases field with ⟨key, fieldValue⟩
                  cases fieldValue with
                  | reference zid => simp [decode] at h
                  | object nestedType nestedFields => simp [decode] at h
                  | list elementType items => simp [decode] at h
                  | quote payload => simp [decode] at h
                  | string digits =>
                      simp only [decode] at h
                      split at h
                      · rename_i shape
                        rcases shape with ⟨rfl, rfl⟩
                        unfold encode
                        rw [toString_eq_of_decodeDecimal_eq_some h]
                      · contradiction

theorem encode_structurallyValid (value : Nat) : (encode value).StructurallyValid := by
  rfl

/-- The pinned executable schema used by the natural-number codec. -/
def checkedSchema : Schema.Checked where
  schema := Schema.Core.z13518Schema
  fuel := 4

theorem encode_schemaValid (value : Nat) : checkedSchema.Valid (encode value) := by
  simp [checkedSchema, Schema.Checked.Valid, Schema.Checked.accepts,
    Schema.Core.z13518Schema, Schema.T.accepts, encode,
    Schema.T.declaredKeys, Schema.T.exclusiveGroupsValid, Schema.T.field?,
    Schema.T.isDeclared, Schema.T.extraKeyAllowed, Schema.StringRule.accepts,
    ZObject.structurallyValid, ZObject.structurallyValidFields, ZObject.keysNoDup]
  simpa only [Nat.toString_eq_repr] using Schema.isNaturalDecimal_toString value

@[simp]
theorem checkedSchema_accepts_encode (value : Nat) :
    checkedSchema.accepts (encode value) = true :=
  encode_schemaValid value

/-- The proof-carrying codec for deployed Z13518 natural-number values. -/
def codec : Codec Nat where
  encode := encode
  decode := decode
  schema := checkedSchema
  encode_schemaValid := encode_schemaValid
  encode_structurallyValid := encode_structurallyValid
  decode_encode := decode_encode
  encode_of_decode_eq_some := encode_of_decode_eq_some

end Natural
end Wikifunctions.Bridge
