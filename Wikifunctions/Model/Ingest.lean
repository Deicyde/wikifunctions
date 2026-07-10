import Wikifunctions.Model.Decode

/-!
# Order-independent wire ingestion

`Decode` characterizes the exact output of the project serializers.  This module is the wider
JSON ingestion boundary: object members are looked up by name after duplicate-key rejection, so
their source order is irrelevant.  Ordinary object fields are sorted before constructing a
`ZObject`, giving permutations of a JSON object the same semantic result.

Both entry points are explicitly fuel-bounded.  Quotation is a hard trust boundary: once an
object is recognized as `Z99`, its `Z99K1` value is retained as `Raw` without recursively
inspecting, sorting, or validating it.
-/

namespace Wikifunctions.Model

/-! ## Duplicate-free object maps -/

/-- Look up a raw object member.  Callers reject duplicate keys before using this operation. -/
def rawField? : List (String × Raw) → String → Option Raw
  | [], _ => none
  | (key, value) :: fields, target =>
      if key == target then some value else rawField? fields target

/-- Remove every member with the given name.  At the ingestion boundary there can be at most
one, because this operation is used only after `rawKeysNoDup` succeeds. -/
def eraseRawField (fields : List (String × Raw)) (target : String) : List (String × Raw) :=
  fields.filter (fun field => field.1 != target)

/-- Retrieve the named member only when it is the object's sole data member. -/
def onlyRawField? (fields : List (String × Raw)) (key : String) : Option Raw :=
  if fields.length == 1 then rawField? fields key else none

/-- Insert a raw object member into lexicographic key order. -/
def insertRawField (field : String × Raw) : List (String × Raw) → List (String × Raw)
  | [] => [field]
  | next :: fields =>
      if field.1 < next.1 then field :: next :: fields
      else next :: insertRawField field fields

/-- Give ordinary object fields a deterministic semantic order. -/
def sortRawFields : List (String × Raw) → List (String × Raw)
  | [] => []
  | field :: fields => insertRawField field (sortRawFields fields)

/-- Look up a decoded semantic field. -/
def zField? : List (Key × ZObject) → Key → Option ZObject
  | [], _ => none
  | (key, value) :: fields, target =>
      if key.raw == target.raw then some value else zField? fields target

/-- Decode ordinary fields with a supplied recursive decoder.  Sorting makes construction
independent of the input JSON member order. -/
def ingestFields (decode : Raw → Option ZObject) (fields : List (String × Raw)) :
    Option (List (Key × ZObject)) := do
  (sortRawFields fields).mapM fun (rawKey, rawValue) => do
    let key ← Key.parse rawKey
    let value ← decode rawValue
    pure (key, value)

/-- Decode a sequence of raw values with a supplied recursive decoder. -/
def ingestValues (decode : Raw → Option ZObject) (values : List Raw) :
    Option (List ZObject) :=
  values.mapM decode

/-! ## Normal-form ingestion -/

/-- Interpret the exceptional bare type markers used inside normal terminal objects.  All other
type expressions are decoded recursively. -/
def ingestNormalType (decode : Raw → Option ZObject) : Raw → Option ZObject
  | .string "Z6" => some (.reference IDs.z6)
  | .string "Z9" => some (.reference IDs.z9)
  | .string "Z99" => some (.reference IDs.z99)
  | raw => decode raw

/-- Recognize the pinned LIST schema's recursive representations of the Z881 function identity.

Besides a direct reference, LIST permits a literal Z8 whose Z8K5 identity recursively denotes
Z881.  Fuel makes malicious cyclic literal identities an ordinary rejection. -/
def normalTypedListFunction : Nat → ZObject → Bool
  | 0, _ => false
  | _ + 1, .reference functionId => functionId == IDs.z881
  | fuel + 1, .object (.reference typeId) fields =>
      typeId == IDs.z8 &&
        match zField? fields Keys.z8k5 with
        | some identity => normalTypedListFunction fuel identity
        | none => false
  | _ + 1, _ => false

/-- Recognize every recursive list-type identity represented by the pinned normal LIST schema.

A list type is either a Z7 call to the direct or literal Z881 function, or a literal Z4 whose
Z4K1 identity recursively denotes such a list type. -/
def normalListElementTypeAux : Nat → ZObject → Option ZObject
  | 0, _ => none
  | fuel + 1, .object (.reference typeId) fields =>
      if typeId == IDs.z7 then
        match zField? fields Keys.z7k1, zField? fields Keys.z881k1 with
        | some function, some elementType =>
            if normalTypedListFunction fuel function then some elementType else none
        | _, _ => none
      else if typeId == IDs.z4 then
        match zField? fields Keys.z4k1 with
        | some identity => normalListElementTypeAux fuel identity
        | none => none
      else
        none
  | _ + 1, _ => none

/-- Recognize a decoded normal list type at an explicit identity-unfolding bound. -/
def normalListElementType? (fuel : Nat) (type : ZObject) : Option ZObject :=
  normalListElementTypeAux fuel type

/-- Decode the data portion of a normal object once its type has been decoded. -/
def ingestNormalObjectData (identityFuel : Nat) (decode : Raw → Option ZObject) (type : ZObject)
    (dataFields : List (String × Raw)) : Option ZObject :=
  match type with
  | .reference zid =>
      if zid.raw == IDs.z6.raw then
        match onlyRawField? dataFields "Z6K1" with
        | some (.string value) => some (.string value)
        | _ => none
      else if zid.raw == IDs.z9.raw then
        match onlyRawField? dataFields "Z9K1" with
        | some (.string value) => (ZID.parse value).map ZObject.reference
        | _ => none
      else if zid.raw == IDs.z99.raw then
        match onlyRawField? dataFields "Z99K1" with
        | some payload => some (.quote payload)
        | none => none
      else
        (ingestFields decode dataFields).map (ZObject.object type)
  | _ =>
      match normalListElementType? identityFuel type with
      | some elementType =>
          if dataFields.isEmpty then
            some (.list elementType [])
          else if dataFields.length == 2 then
            match rawField? dataFields "K1", rawField? dataFields "K2" with
            | some headRaw, some tailRaw =>
                match decode headRaw, decode tailRaw with
                | some head, some (.list tailElementType tail) =>
                    if rawEq tailElementType.toNormal elementType.toNormal then
                      some (.list elementType (head :: tail))
                    else
                      none
                | _, _ => none
            | _, _ => none
          else
            none
      | none => (ingestFields decode dataFields).map (ZObject.object type)

/-- Decode a duplicate-free normal object by named-member lookup. -/
def ingestNormalObject (identityFuel : Nat) (decode : Raw → Option ZObject)
    (fields : List (String × Raw)) : Option ZObject :=
  if rawKeysNoDup fields then
    match rawField? fields "Z1K1" with
    | some typeRaw =>
        match ingestNormalType decode typeRaw with
        | some type => ingestNormalObjectData identityFuel decode type
            (eraseRawField fields "Z1K1")
        | none => none
    | none => none
  else
    none

/-- Ingest normal wire syntax with at most `fuel` recursive object layers. -/
def ingestNormal : Nat → Raw → Option ZObject
  | 0, _ => none
  | fuel + 1, .object fields => ingestNormalObject fuel (ingestNormal fuel) fields
  | _ + 1, _ => none

/-! ## Canonical-form ingestion -/

/-- Decode a duplicate-free canonical object by named-member lookup.  Quoted payloads are
returned before the recursive decoder is applied to them. -/
def ingestCanonicalObject (decode : Raw → Option ZObject)
    (fields : List (String × Raw)) : Option ZObject :=
  if rawKeysNoDup fields then
    match rawField? fields "Z1K1" with
    | some typeRaw =>
        let dataFields := eraseRawField fields "Z1K1"
        match typeRaw with
        | .string "Z6" =>
            match onlyRawField? dataFields "Z6K1" with
            | some (.string value) =>
                if isZID value then some (.string value) else none
            | _ => none
        | .string "Z99" =>
            match onlyRawField? dataFields "Z99K1" with
            | some payload => some (.quote payload)
            | none => none
        | _ =>
            match decode typeRaw, ingestFields decode dataFields with
            | some type, some decodedFields => some (.object type decodedFields)
            | _, _ => none
    | none => none
  else
    none

/-- Ingest canonical wire syntax with at most `fuel` recursive object/list layers. -/
def ingestCanonical : Nat → Raw → Option ZObject
  | 0, _ => none
  | _ + 1, .string value =>
      match ZID.parse value with
      | some zid => some (.reference zid)
      | none => some (.string value)
  | _ + 1, .number _ => none
  | _ + 1, .boolean _ => none
  | _ + 1, .null => none
  | _ + 1, .array [] => none
  | fuel + 1, .array (elementRaw :: itemRaws) =>
      match ingestCanonical fuel elementRaw, ingestValues (ingestCanonical fuel) itemRaws with
      | some elementType, some items => some (.list elementType items)
      | _, _ => none
  | fuel + 1, .object fields => ingestCanonicalObject (ingestCanonical fuel) fields

/-! ## Kernel-checked boundary examples -/

/-- A normal reference terminal with both the terminal and its enclosing use reordered. -/
def reorderedNormalReference (zid : ZID) : Raw :=
  .object [("Z9K1", .string zid.raw), ("Z1K1", .string "Z9")]

/-- Reordering either member of a normal reference terminal does not change ingestion. -/
theorem ingestNormal_reordered_reference :
    ingestNormal 3 (reorderedNormalReference IDs.z40) = some (.reference IDs.z40) := by
  rfl

/-- Two permutations of the same canonical object. -/
def canonicalObjectFirst : Raw :=
  .object
    [("K2", .string "right"), ("Z1K1", .string "Z40"), ("K1", .string "left")]

/-- The same canonical object in a different member order. -/
def canonicalObjectSecond : Raw :=
  .object
    [("K1", .string "left"), ("K2", .string "right"), ("Z1K1", .string "Z40")]

/-- Canonical ingestion is invariant under the demonstrated object-member permutation. -/
theorem ingestCanonical_reordered_object :
    ingestCanonical 3 canonicalObjectFirst = ingestCanonical 3 canonicalObjectSecond := by
  rfl

/-- A deliberately malformed raw payload: duplicate invalid keys and a noncanonical number. -/
def malformedQuotedPayload : Raw :=
  .object [("not a Wikifunctions key", .number "01"), ("not a Wikifunctions key", .null)]

/-- A reordered normal quote whose payload must not pass through the normal decoder. -/
def reorderedNormalQuote : Raw :=
  .object
    [("Z99K1", malformedQuotedPayload),
     ("Z1K1", reorderedNormalReference IDs.z99)]

/-- Normal ingestion preserves malformed quoted syntax byte-for-byte at the `Raw` layer. -/
theorem ingestNormal_malformed_quote_preserved :
    ingestNormal 5 reorderedNormalQuote = some (.quote malformedQuotedPayload) := by
  rfl

/-- A reordered canonical quote around the same deliberately malformed raw payload. -/
def reorderedCanonicalQuote : Raw :=
  .object [("Z99K1", malformedQuotedPayload), ("Z1K1", .string "Z99")]

/-- Canonical ingestion also preserves malformed quoted syntax without recursive inspection. -/
theorem ingestCanonical_malformed_quote_preserved :
    ingestCanonical 1 reorderedCanonicalQuote = some (.quote malformedQuotedPayload) := by
  rfl

/-- A `Z881` type application with all of its fields reordered. -/
def reorderedNormalListType (elementType : Raw) : Raw :=
  .object
    [("Z881K1", elementType),
     ("Z1K1", reorderedNormalReference IDs.z7),
     ("Z7K1", reorderedNormalReference IDs.z881)]

/-- A one-element normal typed list with reordered cell fields and differently ordered repeated
element-type encodings. -/
def reorderedNormalList : Raw :=
  .object
    [("K2",
        .object
          [("Z1K1", reorderedNormalListType (referenceNormal IDs.z6))]),
     ("K1", .object [("Z6K1", .string "value"), ("Z1K1", .string "Z6")]),
     ("Z1K1", reorderedNormalListType (reorderedNormalReference IDs.z6))]

/-- Normal ingestion recognizes reordered `Z881` type applications and list-cell members. -/
theorem ingestNormal_reordered_typed_list :
    ingestNormal 8 reorderedNormalList =
      some (ZObject.list (.reference IDs.z6) [.string "value"]) := by
  simp [reorderedNormalList, reorderedNormalListType, reorderedNormalReference,
    ingestNormal, ingestNormalObject, ingestNormalType, ingestNormalObjectData,
    normalListElementType?, normalListElementTypeAux, normalTypedListFunction,
    rawField?, eraseRawField, onlyRawField?, zField?, ingestFields,
    sortRawFields, insertRawField, rawKeysNoDup, ZID.parse, Key.parse, ZObject.toNormal,
    referenceNormal, IDs.z6, IDs.z7, IDs.z9, IDs.z99, IDs.z881, Keys.z7k1,
    Keys.z881k1, isZID, isKey, positiveDigits, allDigits, globalKeyTail]

/-- A literal Z8 whose identity recursively points to Z881, as permitted by NORMAL/LIST. -/
def literalTypedListFunction : ZObject :=
  .object (.reference IDs.z8) [(Keys.z8k5, .reference IDs.z881)]

/-- A literal Z4 whose identity is a typed-list type application. -/
def literalTypedListType (elementType : ZObject) : ZObject :=
  .object (.reference IDs.z4)
    [(Keys.z4k1,
      .object (.reference IDs.z7)
        [(Keys.z7k1, literalTypedListFunction), (Keys.z881k1, elementType)])]

/-- Recursive literal Z8/Z4 identities preserve the same typed-list element type. -/
theorem normalListElementType_literal_identity :
    normalListElementType? 8 (literalTypedListType (.reference IDs.z6)) =
      some (.reference IDs.z6) := by
  rfl

/-- Normal ingestion classifies an empty list whose type uses recursive literal identities as a
semantic list rather than an ordinary object. -/
theorem ingestNormal_literal_identity_list :
    ingestNormal 16
      (.object [("Z1K1", (literalTypedListType (.reference IDs.z6)).toNormal)]) =
      some (.list (.reference IDs.z6) []) := by
  simp [literalTypedListType, literalTypedListFunction, ingestNormal, ingestNormalObject,
    ingestNormalType, ingestNormalObjectData, normalListElementType?,
    normalListElementTypeAux, normalTypedListFunction, rawField?, eraseRawField,
    onlyRawField?, zField?, ingestFields, sortRawFields, insertRawField, rawKeysNoDup,
    ZID.parse, Key.parse, ZObject.toNormal, toNormalFields, referenceNormal, IDs.z4,
    IDs.z6, IDs.z7, IDs.z8, IDs.z9, IDs.z99, IDs.z881, Keys.z4k1, Keys.z7k1, Keys.z8k5,
    Keys.z881k1, isZID, isKey, positiveDigits, allDigits, globalKeyTail]

@[simp]
theorem ingestNormal_zero (raw : Raw) : ingestNormal 0 raw = none := rfl

@[simp]
theorem ingestCanonical_zero (raw : Raw) : ingestCanonical 0 raw = none := rfl

end Wikifunctions.Model
