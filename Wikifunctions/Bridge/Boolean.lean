import Wikifunctions.Bridge.Codec

/-!
# Codec for Wikifunctions booleans

The deployed Z40 type is a lightweight enumeration.  Its single Z40K1 field contains a reference
to Z41 for true or Z42 for false.  Consequently, boolean *values* are Z40 objects; bare Z41 and
Z42 references are identities, not the complete value representation.  The shape was checked
against revisions Z40/282212, Z41/284088, and Z42/284239.
-/

namespace Wikifunctions.Bridge

open Model

namespace Boolean

/-- The Wikifunctions identity referenced by a Lean boolean. -/
def identity : Bool → ZID
  | false => IDs.z42
  | true => IDs.z41

/-- Decode the identity of a deployed Z40 value. -/
def decodeIdentity (zid : ZID) : Option Bool :=
  if zid = IDs.z41 then some true else if zid = IDs.z42 then some false else none

/-- The deployed semantic Z40 representation of a boolean. -/
def encode (value : Bool) : ZObject :=
  .object (.reference IDs.z40) [(Keys.z40k1, .reference (identity value))]

/-- Decode exactly a deployed Z40 object whose identity is Z41 or Z42. -/
def decode : ZObject → Option Bool
  | .object (.reference typeId) [(key, .reference valueId)] =>
      if typeId = IDs.z40 ∧ key = Keys.z40k1 then decodeIdentity valueId else none
  | _ => none

@[simp]
theorem decodeIdentity_identity (value : Bool) : decodeIdentity (identity value) = some value := by
  cases value <;> rfl

theorem identity_eq_of_decodeIdentity_eq_some {zid : ZID} {value : Bool}
    (h : decodeIdentity zid = some value) : identity value = zid := by
  unfold decodeIdentity at h
  split at h
  · rename_i htrue
    subst zid
    cases value <;> simp_all [identity]
  · split at h
    · rename_i hfalse
      subst zid
      cases value <;> simp_all [identity]
    · contradiction

@[simp]
theorem decode_encode (value : Bool) : decode (encode value) = some value := by
  simpa only [decode, encode, and_self, if_true] using decodeIdentity_identity value

theorem encode_of_decode_eq_some {object : ZObject} {value : Bool}
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
                  | string string => simp [decode] at h
                  | object nestedType nestedFields => simp [decode] at h
                  | list elementType items => simp [decode] at h
                  | quote payload => simp [decode] at h
                  | reference valueId =>
                      simp only [decode] at h
                      split at h
                      · rename_i shape
                        rcases shape with ⟨rfl, rfl⟩
                        unfold encode
                        rw [identity_eq_of_decodeIdentity_eq_some h]
                      · contradiction

theorem encode_structurallyValid (value : Bool) : (encode value).StructurallyValid := by
  rfl

/-- The pinned executable schema used by the Boolean codec. -/
def checkedSchema : Schema.Checked where
  schema := Schema.Core.z40LiteralSchema
  fuel := 4

theorem encode_schemaValid (value : Bool) : checkedSchema.Valid (encode value) := by
  cases value <;> rfl

@[simp]
theorem checkedSchema_accepts_encode (value : Bool) :
    checkedSchema.accepts (encode value) = true :=
  encode_schemaValid value

/-- The proof-carrying codec for deployed Z40/Z41/Z42 boolean values. -/
def codec : Codec Bool where
  encode := encode
  decode := decode
  schema := checkedSchema
  encode_schemaValid := encode_schemaValid
  encode_structurallyValid := encode_structurallyValid
  decode_encode := decode_encode
  encode_of_decode_eq_some := encode_of_decode_eq_some

end Boolean
end Wikifunctions.Bridge
