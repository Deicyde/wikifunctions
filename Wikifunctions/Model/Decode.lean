import Wikifunctions.Model.Serialization
import Lean.Elab.Tactic.Omega

/-!
# Validated wire decoding

This module is the untrusted-data boundary for `Raw`.  Its decoders accept only the canonical
and normal shapes emitted by `Serialization`, validate every ZID and key, reject duplicate raw
object keys, and keep strings distinct from references.

The serializers are deliberately not injective on every inhabitant of the permissive `ZObject`
inductive.  For example, a Z6-shaped ordinary object can have the same canonical wire form as an
explicitly tagged string.  `CanonicalWireSafe` and `NormalWireSafe` state the additional
constructor-disjointness invariant needed for genuine round trips.
-/

namespace Wikifunctions.Model

/-! ## Shared validation helpers -/

mutual
  /-- Structural equality on raw syntax, kept explicit because `Raw` deliberately carries no
  semantic equality instance. -/
  def rawEq : Raw → Raw → Bool
    | .string left, .string right => left == right
    | .number left, .number right => left == right
    | .boolean left, .boolean right => left == right
    | .null, .null => true
    | .array left, .array right => rawListEq left right
    | .object left, .object right => rawFieldListEq left right
    | _, _ => false
  /-- Structural equality on lists of raw values. -/
  def rawListEq : List Raw → List Raw → Bool
    | [], [] => true
    | left :: lefts, right :: rights => rawEq left right && rawListEq lefts rights
    | _, _ => false
  /-- Structural equality on ordered raw object fields. -/
  def rawFieldListEq : List (String × Raw) → List (String × Raw) → Bool
    | [], [] => true
    | (leftKey, leftValue) :: lefts, (rightKey, rightValue) :: rights =>
        leftKey == rightKey && rawEq leftValue rightValue && rawFieldListEq lefts rights
    | _, _ => false
end

mutual
  @[simp]
  theorem rawEq_self (raw : Raw) : rawEq raw raw = true := by
    cases raw with
    | string value => simp [rawEq]
    | number value => simp [rawEq]
    | boolean value => simp [rawEq]
    | null => rfl
    | array values => simp [rawEq, rawListEq_self]
    | object fields => simp [rawEq, rawFieldListEq_self]
  @[simp]
  theorem rawListEq_self (values : List Raw) : rawListEq values values = true := by
    cases values with
    | nil => rfl
    | cons value values => simp [rawListEq, rawEq_self, rawListEq_self]
  @[simp]
  theorem rawFieldListEq_self (fields : List (String × Raw)) :
      rawFieldListEq fields fields = true := by
    cases fields with
    | nil => rfl
    | cons field fields =>
        obtain ⟨key, value⟩ := field
        simp [rawFieldListEq, rawEq_self, rawFieldListEq_self]
end

mutual
  theorem rawEq_eq_true_iff (left right : Raw) : rawEq left right = true ↔ left = right := by
    cases left <;> cases right <;>
      simp [rawEq, rawListEq_eq_true_iff, rawFieldListEq_eq_true_iff]
  theorem rawListEq_eq_true_iff (left right : List Raw) :
      rawListEq left right = true ↔ left = right := by
    cases left with
    | nil => cases right <;> simp [rawListEq]
    | cons left lefts =>
        cases right with
        | nil => simp [rawListEq]
        | cons right rights =>
            simp [rawListEq, rawEq_eq_true_iff, rawListEq_eq_true_iff]
  theorem rawFieldListEq_eq_true_iff
      (left right : List (String × Raw)) :
      rawFieldListEq left right = true ↔ left = right := by
    cases left with
    | nil => cases right <;> simp [rawFieldListEq]
    | cons left lefts =>
        obtain ⟨leftKey, leftValue⟩ := left
        cases right with
        | nil => simp [rawFieldListEq]
        | cons right rights =>
            obtain ⟨rightKey, rightValue⟩ := right
            simp [rawFieldListEq, rawEq_eq_true_iff, rawFieldListEq_eq_true_iff]
end

/-- Whether a raw object has pairwise distinct keys. -/
def rawKeysNoDup : List (String × Raw) → Bool
  | [] => true
  | (key, _) :: fields =>
      !(fields.map (·.1)).contains key && rawKeysNoDup fields

/-- Decode the exact normal form of a reference terminal. -/
def decodeNormalReference : Raw → Option ZID
  | .object [("Z1K1", .string "Z9"), ("Z9K1", .string value)] => ZID.parse value
  | _ => none

/-- A raw value known to occur strictly below another raw value. -/
structure RawChild (parent : Raw) where
  value : Raw
  smaller : sizeOf value < sizeOf parent

/-- Extract the element-type wire value from the exact normal `Z881` type application, together
with the structural decrease used by the total decoder. -/
def decodeNormalTypedListTypeChild : (parent : Raw) → Option (RawChild parent)
  | .object
      [("Z1K1", z7), ("Z7K1", z881), ("Z881K1", elementType)] =>
      match decodeNormalReference z7, decodeNormalReference z881 with
      | some functionType, some listFunction =>
          if functionType.raw = IDs.z7.raw ∧ listFunction.raw = IDs.z881.raw then
            some ⟨elementType, by simp_wf; omega⟩
          else
            none
      | _, _ => none
  | _ => none

/-- Extract the element-type wire value from the exact normal `Z881` type application. -/
def decodeNormalTypedListType (raw : Raw) : Option Raw :=
  (decodeNormalTypedListTypeChild raw).map (·.value)

/-- The reserved interpretation selected by a normal-form type value. -/
inductive NormalTypeView (parent : Raw) where
  | stringType
  | referenceType
  | quoteType
  | typedList (elementType : Raw) (smaller : sizeOf elementType < sizeOf parent)
  | ordinary
deriving Repr

/-- Classify a normal-form type value before decoding the enclosing object. -/
def normalTypeView (raw : Raw) : NormalTypeView raw :=
  match decodeNormalReference raw with
  | some zid =>
      if zid.raw = IDs.z6.raw then
        .stringType
      else if zid.raw = IDs.z9.raw then
        .referenceType
      else if zid.raw = IDs.z99.raw then
        .quoteType
      else
        .ordinary
  | none =>
      match decodeNormalTypedListTypeChild raw with
      | some elementType => .typedList elementType.value elementType.smaller
      | none =>
          match raw with
          | .string "Z6" => .stringType
          | .string "Z9" => .referenceType
          | .string "Z99" => .quoteType
          | _ => .ordinary

@[simp]
theorem decodeNormalReference_referenceNormal (zid : ZID) :
    decodeNormalReference (referenceNormal zid) = some zid := by
  simp [decodeNormalReference, referenceNormal, ZID.parse_raw]

@[simp]
theorem decodeNormalTypedListType_typedListTypeNormal (elementRaw : Raw) :
    decodeNormalTypedListType (typedListTypeNormal elementRaw) = some elementRaw := by
  simp [decodeNormalTypedListType, decodeNormalTypedListTypeChild, typedListTypeNormal,
    decodeNormalReference_referenceNormal, IDs.z7, IDs.z881]

@[simp]
theorem decodeNormalReference_typedListTypeNormal (elementRaw : Raw) :
    decodeNormalReference (typedListTypeNormal elementRaw) = none := by
  simp [decodeNormalReference, typedListTypeNormal]

@[simp]
theorem normalTypeView_referenceNormal_z6 :
    normalTypeView (referenceNormal IDs.z6) = .stringType := by
  simp [normalTypeView, decodeNormalReference_referenceNormal, IDs.z6]

@[simp]
theorem normalTypeView_referenceNormal_z9 :
    normalTypeView (referenceNormal IDs.z9) = .referenceType := by
  simp [normalTypeView, decodeNormalReference_referenceNormal, IDs.z6, IDs.z9]

@[simp]
theorem normalTypeView_referenceNormal_z99 :
    normalTypeView (referenceNormal IDs.z99) = .quoteType := by
  simp [normalTypeView, decodeNormalReference_referenceNormal, IDs.z6, IDs.z9, IDs.z99]

@[simp]
theorem normalTypeView_typedListTypeNormal (elementRaw : Raw) :
    normalTypeView (typedListTypeNormal elementRaw) =
      .typedList elementRaw (by simp [typedListTypeNormal]; omega) := by
  unfold normalTypeView
  rw [decodeNormalReference_typedListTypeNormal]
  simp [decodeNormalTypedListTypeChild, typedListTypeNormal,
    decodeNormalReference_referenceNormal, IDs.z7, IDs.z881]

/-- Whether a normal type is not reserved for a terminal, quote, or typed-list constructor. -/
def normalOrdinaryType (raw : Raw) : Bool :=
  match normalTypeView raw with
  | .ordinary => true
  | _ => false

/-! ## Normal decoding -/

mutual
  /-- Decode evaluator-facing normal form. -/
  def decodeNormal : Raw → Option ZObject
    | .string _ => none
    | .number _ => none
    | .boolean _ => none
    | .null => none
    | .array _ => none
    | .object fields =>
        if rawKeysNoDup fields then
          match fields with
          | ("Z1K1", typeRaw) :: dataFields =>
              match normalTypeView typeRaw with
              | .stringType =>
                  match dataFields with
                  | [("Z6K1", .string value)] => some (.string value)
                  | _ => none
              | .referenceType =>
                  match dataFields with
                  | [("Z9K1", .string value)] =>
                      match ZID.parse value with
                      | some zid => some (.reference zid)
                      | none => none
                  | _ => none
              | .quoteType =>
                  match dataFields with
                  | [("Z99K1", payload)] => some (.quote payload)
                  | _ => none
              | .typedList elementRaw _ =>
                  match decodeNormal elementRaw, decodeNormalListFields elementRaw dataFields with
                  | some elementType, some items => some (.list elementType items)
                  | _, _ => none
              | .ordinary =>
                  match decodeNormal typeRaw, decodeNormalFields dataFields with
                  | some type, some decodedFields => some (.object type decodedFields)
                  | _, _ => none
          | _ => none
        else
          none
  termination_by raw => 4 * sizeOf raw
  /-- Decode the data fields of an ordinary normal-form object. -/
  def decodeNormalFields : List (String × Raw) → Option (List (Key × ZObject))
    | [] => some []
    | (rawKey, rawValue) :: fields =>
        match Key.parse rawKey, decodeNormal rawValue, decodeNormalFields fields with
        | some key, some value, some decodedFields => some ((key, value) :: decodedFields)
        | _, _, _ => none
  termination_by fields => 4 * sizeOf fields + 1
  /-- Decode a normal typed-list cell after its element type has been fixed. -/
  def decodeNormalListFields (elementRaw : Raw) :
      List (String × Raw) → Option (List ZObject)
    | [] => some []
    | [("K1", rawValue), ("K2", rawTail)] =>
        match decodeNormal rawValue, decodeNormalListTail elementRaw rawTail with
        | some value, some values => some (value :: values)
        | _, _ => none
    | _ => none
  termination_by fields => 4 * sizeOf fields + 1
  /-- Decode a typed-list tail, requiring every cell to repeat the identical element-type wire
  value.  This rejects malformed or heterogeneously typed tails. -/
  def decodeNormalListTail (elementRaw : Raw) : Raw → Option (List ZObject)
    | .object fields =>
        if rawKeysNoDup fields then
          match fields with
          | ("Z1K1", typeRaw) :: dataFields =>
              match decodeNormalTypedListType typeRaw with
              | some repeatedElementRaw =>
                  if rawEq repeatedElementRaw elementRaw then
                    decodeNormalListFields elementRaw dataFields
                  else
                    none
              | none => none
          | _ => none
        else
          none
    | _ => none
  termination_by raw => 4 * sizeOf raw + 2
end

/-! ## Canonical decoding -/

/-- The reserved interpretation selected by a canonical object type. -/
inductive CanonicalTypeView where
  | stringType
  | quoteType
  | ordinary
deriving Repr

/-- Classify a canonical object type before decoding its data fields. -/
def canonicalTypeView : Raw → CanonicalTypeView
  | .string "Z6" => .stringType
  | .string "Z99" => .quoteType
  | _ => .ordinary

/-- Whether a canonical type is not reserved for a tagged string or quote. -/
def canonicalOrdinaryType (raw : Raw) : Bool :=
  match canonicalTypeView raw with
  | .ordinary => true
  | _ => false

mutual
  /-- Decode canonical wire form.  Bare valid ZIDs are references; ZID-shaped strings therefore
  require the explicit canonical Z6 wrapper emitted by `Canonical.toRaw`. -/
  def decodeCanonical : Raw → Option ZObject
    | .string value =>
        match ZID.parse value with
        | some zid => some (.reference zid)
        | none => some (.string value)
    | .number _ => none
    | .boolean _ => none
    | .null => none
    | .array [] => none
    | .array (elementRaw :: itemRaws) =>
        match decodeCanonical elementRaw, decodeCanonicalList itemRaws with
        | some elementType, some items => some (.list elementType items)
        | _, _ => none
    | .object fields =>
        if rawKeysNoDup fields then
          match fields with
          | ("Z1K1", typeRaw) :: dataFields =>
              match canonicalTypeView typeRaw with
              | .stringType =>
                  match dataFields with
                  | [("Z6K1", .string value)] =>
                      if isZID value then some (.string value) else none
                  | _ => none
              | .quoteType =>
                  match dataFields with
                  | [("Z99K1", payload)] => some (.quote payload)
                  | _ => none
              | .ordinary =>
                  match decodeCanonical typeRaw, decodeCanonicalFields dataFields with
                  | some type, some decodedFields => some (.object type decodedFields)
                  | _, _ => none
          | _ => none
        else
          none
  termination_by raw => 3 * sizeOf raw
  /-- Decode canonical data fields, validating every key. -/
  def decodeCanonicalFields : List (String × Raw) → Option (List (Key × ZObject))
    | [] => some []
    | (rawKey, rawValue) :: fields =>
        match Key.parse rawKey, decodeCanonical rawValue, decodeCanonicalFields fields with
        | some key, some value, some decodedFields => some ((key, value) :: decodedFields)
        | _, _, _ => none
  termination_by fields => 3 * sizeOf fields + 1
  /-- Decode canonical list items. -/
  def decodeCanonicalList : List Raw → Option (List ZObject)
    | [] => some []
    | rawValue :: values =>
        match decodeCanonical rawValue, decodeCanonicalList values with
        | some value, some decodedValues => some (value :: decodedValues)
        | _, _ => none
  termination_by values => 3 * sizeOf values + 1
end

/-! ## The injective serialization domain -/

mutual
  /-- Constructor-disjointness and recursive decodability for normal form. -/
  def normalShapeSafe : ZObject → Bool
    | .string _ => true
    | .reference _ => true
    | .object type fields =>
        normalOrdinaryType type.toNormal &&
          rawKeysNoDup (("Z1K1", type.toNormal) :: toNormalFields fields) &&
          normalShapeSafe type && normalFieldsShapeSafe fields
    | .list elementType items =>
        normalShapeSafe elementType && normalListShapeSafe items
    | .quote _ => true
  /-- Recursive normal-form safety for ordinary fields. -/
  def normalFieldsShapeSafe : List (Key × ZObject) → Bool
    | [] => true
    | (_, value) :: fields => normalShapeSafe value && normalFieldsShapeSafe fields
  /-- Recursive normal-form safety for list items. -/
  def normalListShapeSafe : List ZObject → Bool
    | [] => true
    | value :: values => normalShapeSafe value && normalListShapeSafe values
end

mutual
  /-- Constructor-disjointness and recursive decodability for canonical form. -/
  def canonicalShapeSafe : ZObject → Bool
    | .string _ => true
    | .reference _ => true
    | .object type fields =>
        canonicalOrdinaryType (canonicalize type).toRaw &&
          rawKeysNoDup
            (("Z1K1", (canonicalize type).toRaw) :: toRawFields (canonicalizeFields fields)) &&
          canonicalShapeSafe type && canonicalFieldsShapeSafe fields
    | .list elementType items =>
        canonicalShapeSafe elementType && canonicalListShapeSafe items
    | .quote _ => true
  /-- Recursive canonical-form safety for ordinary fields. -/
  def canonicalFieldsShapeSafe : List (Key × ZObject) → Bool
    | [] => true
    | (_, value) :: fields => canonicalShapeSafe value && canonicalFieldsShapeSafe fields
  /-- Recursive canonical-form safety for list items. -/
  def canonicalListShapeSafe : List ZObject → Bool
    | [] => true
    | value :: values => canonicalShapeSafe value && canonicalListShapeSafe values
end

/-- Values on which the normal serializer is injective and the strict decoder is a left inverse. -/
def NormalWireSafe (z : ZObject) : Prop :=
  z.StructurallyValid ∧ normalShapeSafe z = true

/-- Values on which the canonical serializer is injective and the strict decoder is a left
inverse. -/
def CanonicalWireSafe (z : ZObject) : Prop :=
  z.StructurallyValid ∧ canonicalShapeSafe z = true

/-- The reusable wire-domain contract for values that round-trip through both representations. -/
def WireSafe (z : ZObject) : Prop :=
  NormalWireSafe z ∧ CanonicalWireSafe z

/-! ## Basic terminal round trips -/

@[simp]
theorem decodeNormal_string (value : String) :
    decodeNormal (ZObject.string value).toNormal = some (.string value) := by
  simp [ZObject.toNormal, stringNormal, decodeNormal, rawKeysNoDup, normalTypeView,
    decodeNormalReference, decodeNormalTypedListTypeChild]

@[simp]
theorem decodeNormal_reference (zid : ZID) :
    decodeNormal (ZObject.reference zid).toNormal = some (.reference zid) := by
  simp [ZObject.toNormal, referenceNormal, decodeNormal, rawKeysNoDup, normalTypeView,
    decodeNormalReference, decodeNormalTypedListTypeChild, ZID.parse_raw]

@[simp]
theorem decodeCanonical_string (value : String) :
    decodeCanonical (canonicalize (.string value)).toRaw = some (.string value) := by
  by_cases h : isZID value = true
  · simp [canonicalize, Canonical.toRaw, h, decodeCanonical, rawKeysNoDup,
      canonicalTypeView]
  · simp [canonicalize, Canonical.toRaw, h, decodeCanonical, ZID.parse]

@[simp]
theorem decodeCanonical_reference (zid : ZID) :
    decodeCanonical (canonicalize (.reference zid)).toRaw = some (.reference zid) := by
  simp [canonicalize, Canonical.toRaw, decodeCanonical, ZID.parse, zid.valid]

theorem normalOrdinaryType_eq_true_iff (raw : Raw) :
    normalOrdinaryType raw = true ↔ normalTypeView raw = .ordinary := by
  unfold normalOrdinaryType
  cases normalTypeView raw <;> simp

theorem canonicalOrdinaryType_eq_true_iff (raw : Raw) :
    canonicalOrdinaryType raw = true ↔ canonicalTypeView raw = .ordinary := by
  unfold canonicalOrdinaryType
  cases canonicalTypeView raw <;> simp

/-! ## Normal renderer/decoder round trip -/

mutual
  /-- The strict normal decoder is a left inverse on the normal shape-safe domain. -/
  theorem decodeNormal_toNormal_of_shape_safe (z : ZObject)
      (safe : normalShapeSafe z = true) :
      decodeNormal z.toNormal = some z := by
    cases z with
    | string value => exact decodeNormal_string value
    | reference zid => exact decodeNormal_reference zid
    | object type fields =>
        simp only [normalShapeSafe, Bool.and_eq_true] at safe
        have typeOrdinary := safe.1.1.1
        have keysUnique := safe.1.1.2
        have typeSafe := safe.1.2
        have fieldsSafe := safe.2
        have typeView : normalTypeView type.toNormal = .ordinary :=
          (normalOrdinaryType_eq_true_iff type.toNormal).mp typeOrdinary
        simp only [ZObject.toNormal]
        unfold decodeNormal
        simp [keysUnique, typeView, decodeNormal_toNormal_of_shape_safe type typeSafe,
          decodeNormalFields_toNormalFields_of_shape_safe fields fieldsSafe]
    | list elementType items =>
        simp only [normalShapeSafe, Bool.and_eq_true] at safe
        obtain ⟨elementTypeSafe, itemsSafe⟩ := safe
        cases items with
        | nil =>
            simp [ZObject.toNormal, toNormalTypedList, decodeNormal, decodeNormalListFields,
              rawKeysNoDup,
              normalTypeView_typedListTypeNormal,
              decodeNormal_toNormal_of_shape_safe elementType elementTypeSafe]
        | cons value values =>
            simp only [normalListShapeSafe, Bool.and_eq_true] at itemsSafe
            obtain ⟨valueSafe, valuesSafe⟩ := itemsSafe
            simp [ZObject.toNormal, toNormalTypedList, decodeNormal, decodeNormalListFields,
              rawKeysNoDup,
              normalTypeView_typedListTypeNormal,
              decodeNormal_toNormal_of_shape_safe elementType elementTypeSafe,
              decodeNormal_toNormal_of_shape_safe value valueSafe,
              decodeNormalListTail_toNormalTypedList_of_shape_safe elementType values
                elementTypeSafe valuesSafe]
    | quote payload =>
        simp [ZObject.toNormal, decodeNormal, rawKeysNoDup,
          normalTypeView_referenceNormal_z99]
  /-- Normal decoding commutes with the serializer on an ordinary field list. -/
  theorem decodeNormalFields_toNormalFields_of_shape_safe
      (fields : List (Key × ZObject)) (safe : normalFieldsShapeSafe fields = true) :
      decodeNormalFields (toNormalFields fields) = some fields := by
    cases fields with
    | nil => simp [toNormalFields, decodeNormalFields]
    | cons field fields =>
        obtain ⟨key, value⟩ := field
        simp only [normalFieldsShapeSafe, Bool.and_eq_true] at safe
        obtain ⟨valueSafe, fieldsSafe⟩ := safe
        simp [toNormalFields, decodeNormalFields, Key.parse_raw,
          decodeNormal_toNormal_of_shape_safe value valueSafe,
          decodeNormalFields_toNormalFields_of_shape_safe fields fieldsSafe]
  /-- A normal typed-list tail decodes with exactly the repeated element type. -/
  theorem decodeNormalListTail_toNormalTypedList_of_shape_safe
      (elementType : ZObject) (items : List ZObject)
      (elementTypeSafe : normalShapeSafe elementType = true)
      (itemsSafe : normalListShapeSafe items = true) :
      decodeNormalListTail elementType.toNormal (toNormalTypedList elementType items) =
        some items := by
    cases items with
    | nil =>
        simp [toNormalTypedList, decodeNormalListTail, decodeNormalListFields, rawKeysNoDup,
          decodeNormalTypedListType_typedListTypeNormal, rawEq_self]
    | cons value values =>
        simp only [normalListShapeSafe, Bool.and_eq_true] at itemsSafe
        obtain ⟨valueSafe, valuesSafe⟩ := itemsSafe
        simp [toNormalTypedList, decodeNormalListTail, decodeNormalListFields, rawKeysNoDup,
          decodeNormalTypedListType_typedListTypeNormal, rawEq_self,
          decodeNormal_toNormal_of_shape_safe value valueSafe,
          decodeNormalListTail_toNormalTypedList_of_shape_safe elementType values
            elementTypeSafe valuesSafe]
end

/-! ## Canonical renderer/decoder round trip -/

mutual
  /-- The strict canonical decoder is a left inverse on the canonical shape-safe domain. -/
  theorem decodeCanonical_toRaw_of_shape_safe (z : ZObject)
      (safe : canonicalShapeSafe z = true) :
      decodeCanonical (canonicalize z).toRaw = some z := by
    cases z with
    | string value => exact decodeCanonical_string value
    | reference zid => exact decodeCanonical_reference zid
    | object type fields =>
        simp only [canonicalShapeSafe, Bool.and_eq_true] at safe
        have typeOrdinary := safe.1.1.1
        have keysUnique := safe.1.1.2
        have typeSafe := safe.1.2
        have fieldsSafe := safe.2
        have typeView : canonicalTypeView (canonicalize type).toRaw = .ordinary :=
          (canonicalOrdinaryType_eq_true_iff (canonicalize type).toRaw).mp typeOrdinary
        simp only [canonicalize, Canonical.toRaw]
        unfold decodeCanonical
        simp [keysUnique, typeView, decodeCanonical_toRaw_of_shape_safe type typeSafe,
          decodeCanonicalFields_toRawFields_of_shape_safe fields fieldsSafe]
    | list elementType items =>
        simp only [canonicalShapeSafe, Bool.and_eq_true] at safe
        obtain ⟨elementTypeSafe, itemsSafe⟩ := safe
        simp [canonicalize, Canonical.toRaw, decodeCanonical,
          decodeCanonical_toRaw_of_shape_safe elementType elementTypeSafe,
          decodeCanonicalList_toRawList_of_shape_safe items itemsSafe]
    | quote payload =>
        simp [canonicalize, Canonical.toRaw, decodeCanonical, rawKeysNoDup,
          canonicalTypeView]
  /-- Canonical decoding commutes with the serializer on an ordinary field list. -/
  theorem decodeCanonicalFields_toRawFields_of_shape_safe
      (fields : List (Key × ZObject)) (safe : canonicalFieldsShapeSafe fields = true) :
      decodeCanonicalFields (toRawFields (canonicalizeFields fields)) = some fields := by
    cases fields with
    | nil => simp [canonicalizeFields, toRawFields, decodeCanonicalFields]
    | cons field fields =>
        obtain ⟨key, value⟩ := field
        simp only [canonicalFieldsShapeSafe, Bool.and_eq_true] at safe
        obtain ⟨valueSafe, fieldsSafe⟩ := safe
        simp [canonicalizeFields, toRawFields, decodeCanonicalFields, Key.parse_raw,
          decodeCanonical_toRaw_of_shape_safe value valueSafe,
          decodeCanonicalFields_toRawFields_of_shape_safe fields fieldsSafe]
  /-- Canonical decoding commutes with the serializer on list items. -/
  theorem decodeCanonicalList_toRawList_of_shape_safe
      (values : List ZObject) (safe : canonicalListShapeSafe values = true) :
      decodeCanonicalList (toRawList (canonicalizeList values)) = some values := by
    cases values with
    | nil => simp [canonicalizeList, toRawList, decodeCanonicalList]
    | cons value values =>
        simp only [canonicalListShapeSafe, Bool.and_eq_true] at safe
        obtain ⟨valueSafe, valuesSafe⟩ := safe
        simp [canonicalizeList, toRawList, decodeCanonicalList,
          decodeCanonical_toRaw_of_shape_safe value valueSafe,
          decodeCanonicalList_toRawList_of_shape_safe values valuesSafe]
end

/-! ## Public round-trip contracts -/

/-- Every normal wire-safe semantic value survives normal rendering and strict decoding. -/
theorem decodeNormal_toNormal (z : ZObject) (safe : NormalWireSafe z) :
    decodeNormal z.toNormal = some z :=
  decodeNormal_toNormal_of_shape_safe z safe.2

/-- Every canonical wire-safe semantic value survives canonical rendering and strict decoding. -/
theorem decodeCanonical_canonicalize_toRaw (z : ZObject) (safe : CanonicalWireSafe z) :
    decodeCanonical (canonicalize z).toRaw = some z :=
  decodeCanonical_toRaw_of_shape_safe z safe.2

/-- The combined wire-domain contract supplies the normal round trip. -/
theorem decodeNormal_toNormal_of_wireSafe (z : ZObject) (safe : WireSafe z) :
    decodeNormal z.toNormal = some z :=
  decodeNormal_toNormal z safe.1

/-- The combined wire-domain contract supplies the canonical round trip. -/
theorem decodeCanonical_canonicalize_toRaw_of_wireSafe (z : ZObject) (safe : WireSafe z) :
    decodeCanonical (canonicalize z).toRaw = some z :=
  decodeCanonical_canonicalize_toRaw z safe.2

/-! ## Explicit trust-boundary checks and unavoidable collisions -/

/-- A structurally valid ordinary object whose canonical rendering collides with the tagged
string `"Z40"`. -/
def canonicalStringCollisionObject : ZObject :=
  .object (.reference IDs.z6) [(Keys.z6k1, .reference IDs.z40)]

theorem canonicalStringCollisionObject_structurallyValid :
    canonicalStringCollisionObject.StructurallyValid := by
  decide

/-- Structural validity alone cannot imply the canonical round trip. -/
theorem canonical_string_object_collision :
    (canonicalize (.string "Z40")).toRaw =
      (canonicalize canonicalStringCollisionObject).toRaw := rfl

theorem canonicalStringCollisionObject_not_shapeSafe :
    canonicalShapeSafe canonicalStringCollisionObject = false := by
  rfl

/-- A structurally valid ordinary object whose normal rendering collides with quotation. -/
def normalQuoteCollisionObject : ZObject :=
  .object (.reference IDs.z99) [(Keys.z99k1, .reference IDs.z40)]

theorem normalQuoteCollisionObject_structurallyValid :
    normalQuoteCollisionObject.StructurallyValid := by
  decide

theorem normal_quote_object_collision :
    (ZObject.quote (referenceNormal IDs.z40)).toNormal = normalQuoteCollisionObject.toNormal := by
  simp [normalQuoteCollisionObject, ZObject.toNormal, toNormalFields, Keys.z99k1]

theorem normalQuoteCollisionObject_not_shapeSafe :
    normalShapeSafe normalQuoteCollisionObject = false := by
  simp only [normalQuoteCollisionObject, normalShapeSafe]
  have typeNormal : (ZObject.reference IDs.z99).toNormal = referenceNormal IDs.z99 := by
    simp [ZObject.toNormal]
  rw [typeNormal]
  simp [normalOrdinaryType, normalTypeView_referenceNormal_z99]

/-- The semantic type object whose normal form is the type-level `Z881 elementType` call. -/
def semanticTypedListType (elementType : ZObject) : ZObject :=
  .object (.reference IDs.z7)
    [(Keys.z7k1, .reference IDs.z881), (Keys.z881k1, elementType)]

/-- Empty typed lists also collide with ordinary empty objects having the rendered list type. -/
theorem normal_empty_list_object_collision (elementType : ZObject) :
    (ZObject.list elementType []).toNormal =
      (ZObject.object (semanticTypedListType elementType) []).toNormal := by
  simp [semanticTypedListType, ZObject.toNormal, toNormalFields, toNormalTypedList,
    typedListTypeNormal, Keys.z7k1, Keys.z881k1]

/-- Duplicate object keys are rejected before any constructor interpretation. -/
theorem decodeCanonical_rejects_duplicate_keys :
    decodeCanonical
        (.object [("Z1K1", .string "Z7"), ("Z1K1", .string "Z8")]) = none := by
  unfold decodeCanonical
  simp [rawKeysNoDup]

/-- Duplicate keys are rejected in normal form as well. -/
theorem decodeNormal_rejects_duplicate_keys :
    decodeNormal
        (.object [("Z1K1", .string "Z7"), ("Z1K1", .string "Z8")]) = none := by
  unfold decodeNormal
  simp [rawKeysNoDup]

/-- Invalid reference identifiers are rejected at the normal wire boundary. -/
theorem decodeNormal_rejects_invalid_reference :
    decodeNormal
        (.object [("Z1K1", .string "Z9"), ("Z9K1", .string "Z0")]) = none := by
  unfold decodeNormal
  simp [rawKeysNoDup, normalTypeView, decodeNormalReference,
    decodeNormalTypedListTypeChild, ZID.parse, isZID, positiveDigits]

/-- A typed-list tail whose repeated element type differs from its head is rejected. -/
theorem decodeNormalListTail_rejects_changed_element_type :
    decodeNormalListTail (referenceNormal IDs.z6)
        (.object
          [("Z1K1", typedListTypeNormal (referenceNormal IDs.z9))]) = none := by
  unfold decodeNormalListTail
  simp [rawKeysNoDup, decodeNormalTypedListType_typedListTypeNormal, rawEq,
    rawFieldListEq, referenceNormal, IDs.z6, IDs.z9]

end Wikifunctions.Model
