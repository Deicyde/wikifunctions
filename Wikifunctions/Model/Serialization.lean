import Wikifunctions.Model.ZObject

/-!
# Canonical and normal serialization

`ZObject` is the semantic value language.  This module supplies a separate semantic canonical
representation over the lossless `Raw` syntax defined alongside Z99 quotation:

* `Canonical` preserves the semantic distinction between strings and references while describing
  canonical form.

`canonicalize` and `normalize` are structural inverses.  JSON rendering happens only afterwards,
so an explicit canonical Z6 string such as `"Z40"` cannot be reinterpreted as a reference.
-/

namespace Wikifunctions.Model

/-- Semantic canonical form.

Unlike raw JSON, `string` and `reference` are distinct constructors.  `quote` retains its raw
payload exactly because quotation suppresses recursive decoding and canonicalization. -/
inductive Canonical where
  | string : String → Canonical
  | reference : ZID → Canonical
  | object : Canonical → List (Key × Canonical) → Canonical
  | list : Canonical → List Canonical → Canonical
  | quote : Raw → Canonical
deriving Repr

mutual
  /-- Convert a semantic value to semantic canonical form. -/
  def canonicalize : ZObject → Canonical
    | .string value => .string value
    | .reference zid => .reference zid
    | .object type fields => .object (canonicalize type) (canonicalizeFields fields)
    | .list elementType items => .list (canonicalize elementType) (canonicalizeList items)
    | .quote payload => .quote payload
  /-- Canonicalize object fields. -/
  def canonicalizeFields : List (Key × ZObject) → List (Key × Canonical)
    | [] => []
    | (key, value) :: fields => (key, canonicalize value) :: canonicalizeFields fields
  /-- Canonicalize list values. -/
  def canonicalizeList : List ZObject → List Canonical
    | [] => []
    | value :: values => canonicalize value :: canonicalizeList values
end

mutual
  /-- Convert semantic canonical form back to a semantic value. -/
  def normalize : Canonical → ZObject
    | .string value => .string value
    | .reference zid => .reference zid
    | .object type fields => .object (normalize type) (normalizeFields fields)
    | .list elementType items => .list (normalize elementType) (normalizeList items)
    | .quote payload => .quote payload
  /-- Normalize object fields. -/
  def normalizeFields : List (Key × Canonical) → List (Key × ZObject)
    | [] => []
    | (key, value) :: fields => (key, normalize value) :: normalizeFields fields
  /-- Normalize list values. -/
  def normalizeList : List Canonical → List ZObject
    | [] => []
    | value :: values => normalize value :: normalizeList values
end

mutual
  /-- Normalizing a canonicalized value returns the original semantic value. -/
  theorem normalize_canonicalize (z : ZObject) : normalize (canonicalize z) = z := by
    cases z with
    | string value => rfl
    | reference zid => rfl
    | object type fields =>
        simp only [canonicalize, normalize]
        rw [normalize_canonicalize type, normalizeFields_canonicalizeFields fields]
    | list elementType items =>
        simp only [canonicalize, normalize]
        rw [normalize_canonicalize elementType, normalizeList_canonicalizeList items]
    | quote payload => rfl
  /-- Normalizing canonicalized object fields returns the original fields. -/
  theorem normalizeFields_canonicalizeFields (fields : List (Key × ZObject)) :
      normalizeFields (canonicalizeFields fields) = fields := by
    cases fields with
    | nil => rfl
    | cons field fields =>
        obtain ⟨key, value⟩ := field
        simp only [canonicalizeFields, normalizeFields]
        rw [normalize_canonicalize value, normalizeFields_canonicalizeFields fields]
  /-- Normalizing a canonicalized list returns the original list. -/
  theorem normalizeList_canonicalizeList (values : List ZObject) :
      normalizeList (canonicalizeList values) = values := by
    cases values with
    | nil => rfl
    | cons value values =>
        simp only [canonicalizeList, normalizeList]
        rw [normalize_canonicalize value, normalizeList_canonicalizeList values]
end

mutual
  /-- Canonicalizing a normalized value returns the original canonical value. -/
  theorem canonicalize_normalize (value : Canonical) :
      canonicalize (normalize value) = value := by
    cases value with
    | string value => rfl
    | reference zid => rfl
    | object type fields =>
        simp only [normalize, canonicalize]
        rw [canonicalize_normalize type, canonicalizeFields_normalizeFields fields]
    | list elementType items =>
        simp only [normalize, canonicalize]
        rw [canonicalize_normalize elementType, canonicalizeList_normalizeList items]
    | quote payload => rfl
  /-- Canonicalizing normalized object fields returns the original fields. -/
  theorem canonicalizeFields_normalizeFields (fields : List (Key × Canonical)) :
      canonicalizeFields (normalizeFields fields) = fields := by
    cases fields with
    | nil => rfl
    | cons field fields =>
        obtain ⟨key, value⟩ := field
        simp only [normalizeFields, canonicalizeFields]
        rw [canonicalize_normalize value, canonicalizeFields_normalizeFields fields]
  /-- Canonicalizing a normalized list returns the original list. -/
  theorem canonicalizeList_normalizeList (values : List Canonical) :
      canonicalizeList (normalizeList values) = values := by
    cases values with
    | nil => rfl
    | cons value values =>
        simp only [normalizeList, canonicalizeList]
        rw [canonicalize_normalize value, canonicalizeList_normalizeList values]
end

/-! ## Raw normal form -/

/-- The normal wire encoding of a reference terminal. -/
def referenceNormal (zid : ZID) : Raw :=
  .object [("Z1K1", .string "Z9"), ("Z9K1", .string zid.raw)]

/-- The normal wire encoding of a string terminal. -/
def stringNormal (value : String) : Raw :=
  .object [("Z1K1", .string "Z6"), ("Z6K1", .string value)]

/-- Render the type-level `Z881 elementType` call used by normal typed lists. -/
def typedListTypeNormal (elementType : Raw) : Raw :=
  .object
    [("Z1K1", referenceNormal IDs.z7),
     ("Z7K1", referenceNormal IDs.z881),
     ("Z881K1", elementType)]

mutual
  /-- Render a semantic value in evaluator-facing normal form. -/
  def ZObject.toNormal : ZObject → Raw
    | .string value => stringNormal value
    | .reference zid => referenceNormal zid
    | .object type fields =>
        .object (("Z1K1", type.toNormal) :: toNormalFields fields)
    | .list elementType items => toNormalTypedList elementType items
    | .quote payload =>
        .object
          [("Z1K1", referenceNormal IDs.z99), ("Z99K1", payload)]
  termination_by z => 2 * sizeOf z
  /-- Render ordinary object fields in normal form. -/
  def toNormalFields : List (Key × ZObject) → List (String × Raw)
    | [] => []
    | (key, value) :: fields => (key.raw, value.toNormal) :: toNormalFields fields
  termination_by fields => 2 * sizeOf fields + 1
  /-- Render a typed list as normal-form `Z881` cons cells. -/
  def toNormalTypedList (elementType : ZObject) : List ZObject → Raw
    | [] => .object [("Z1K1", typedListTypeNormal elementType.toNormal)]
    | value :: values =>
        .object
          [("Z1K1", typedListTypeNormal elementType.toNormal),
           ("K1", value.toNormal),
           ("K2", toNormalTypedList elementType values)]
  termination_by items => 2 * (sizeOf elementType + sizeOf items) + 1
end

/-! ## Raw canonical form -/

mutual
  /-- Render semantic canonical form as canonical JSON-shaped syntax. -/
  def Canonical.toRaw : Canonical → Raw
    | .string value =>
        if isZID value then
          .object [("Z1K1", .string "Z6"), ("Z6K1", .string value)]
        else
          .string value
    | .reference zid => .string zid.raw
    | .object type fields => .object (("Z1K1", type.toRaw) :: toRawFields fields)
    | .list elementType items => .array (elementType.toRaw :: toRawList items)
    | .quote payload =>
        .object [("Z1K1", .string "Z99"), ("Z99K1", payload)]
  /-- Render canonical object fields. -/
  def toRawFields : List (Key × Canonical) → List (String × Raw)
    | [] => []
    | (key, value) :: fields => (key.raw, value.toRaw) :: toRawFields fields
  /-- Render canonical list contents. -/
  def toRawList : List Canonical → List Raw
    | [] => []
    | value :: values => value.toRaw :: toRawList values
end

/-- A ZID-shaped Z6 string remains explicitly tagged in canonical JSON. -/
theorem canonical_zid_shaped_string :
    (canonicalize (.string "Z40")).toRaw =
      .object [("Z1K1", .string "Z6"), ("Z6K1", .string "Z40")] := rfl

/-- References use the bare canonical ZID syntax. -/
theorem canonical_reference :
    (canonicalize (.reference IDs.z40)).toRaw = .string "Z40" := rfl

/-- Quote payloads are emitted exactly and are not recursively decoded or canonicalized. -/
theorem canonical_quote_raw :
    (canonicalize (.quote (stringNormal "Z40"))).toRaw =
      .object
        [("Z1K1", .string "Z99"),
         ("Z99K1", .object [("Z1K1", .string "Z6"), ("Z6K1", .string "Z40")])] := by
  rfl

end Wikifunctions.Model
