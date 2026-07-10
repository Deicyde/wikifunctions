/-!
# Semantic ZObjects

This module separates validated Wikifunctions values from their JSON encodings.  In particular,
strings and references are different constructors even though canonical JSON renders both with
JSON strings.  This prevents the canonical/normal ambiguity from entering the semantic model.

The constructors are the semantic cases used by the evaluator:

* `string` and `reference` are the two terminal values;
* `object` stores its type separately from its data fields;
* `list` is a typed list, whose normal encoding is the `Z881` cons representation;
* `quote` retains lossless raw syntax and makes it opaque to decoding, validation, and resolution.

Identifiers and keys carry proofs of the grammar enforced by function-schemata.  Raw syntax is
co-located here only because Z99 quotation must be able to retain malformed, unevaluated input.
-/

namespace Wikifunctions.Model

/-! ## Validated identifiers -/

/-- Every character in `cs` is an ASCII digit. -/
def allDigits : List Char → Bool
  | [] => true
  | c :: cs => c.isDigit && allDigits cs

/-- A nonempty decimal numeral with no leading zero. -/
def positiveDigits : List Char → Bool
  | [] => false
  | c :: cs => c.isDigit && c != '0' && allDigits cs

/-- The part of a global key following its first ZID digit. -/
def globalKeyTail : List Char → Bool
  | [] => false
  | 'K' :: digits => positiveDigits digits
  | c :: cs => c.isDigit && globalKeyTail cs

/-- Whether `s` is a valid ZID: `Z` followed by a positive decimal numeral. -/
def isZID (s : String) : Bool :=
  match s.toList with
  | 'Z' :: digits => positiveDigits digits
  | _ => false

/-- Whether `s` is a Wikifunctions object key.

Besides local (`K1`) and global (`Z7K1`) keys, Z7's pinned normal schema permits a bare ZID
(`Z123`) as a dynamic argument key. -/
def isKey (s : String) : Bool :=
  isZID s ||
    match s.toList with
    | 'K' :: digits => positiveDigits digits
    | 'Z' :: digit :: rest => digit.isDigit && digit != '0' && globalKeyTail rest
    | _ => false

/-- A validated Wikifunctions object identifier. -/
structure ZID where
  raw : String
  valid : isZID raw = true
deriving Repr, DecidableEq

namespace ZID

/-- Validate an untrusted string as a ZID. -/
def parse (s : String) : Option ZID :=
  if h : isZID s = true then some ⟨s, h⟩ else none

@[simp]
theorem parse_raw (zid : ZID) : parse zid.raw = some zid := by
  cases zid with
  | mk raw valid => simp [parse, valid]

end ZID

/-- A validated Wikifunctions key, including Z7's bare-ZID dynamic-key case. -/
structure Key where
  raw : String
  valid : isKey raw = true
deriving Repr, DecidableEq

namespace Key

/-- Validate an untrusted string as a key. -/
def parse (s : String) : Option Key :=
  if h : isKey s = true then some ⟨s, h⟩ else none

@[simp]
theorem parse_raw (key : Key) : parse key.raw = some key := by
  cases key with
  | mk raw valid => simp [parse, valid]

end Key

/-! ## Reserved identifiers and keys

These constants are the small kernel vocabulary needed by the representation, evaluator, and
WikiLean bridge.  Application-specific ZIDs remain data and are validated with `ZID.parse`.
-/

namespace IDs

def z1 : ZID := ⟨"Z1", by decide⟩
def z4 : ZID := ⟨"Z4", by decide⟩
def z6 : ZID := ⟨"Z6", by decide⟩
def z7 : ZID := ⟨"Z7", by decide⟩
def z8 : ZID := ⟨"Z8", by decide⟩
def z9 : ZID := ⟨"Z9", by decide⟩
def z14 : ZID := ⟨"Z14", by decide⟩
def z16 : ZID := ⟨"Z16", by decide⟩
def z18 : ZID := ⟨"Z18", by decide⟩
def z22 : ZID := ⟨"Z22", by decide⟩
def z24 : ZID := ⟨"Z24", by decide⟩
def z40 : ZID := ⟨"Z40", by decide⟩
def z41 : ZID := ⟨"Z41", by decide⟩
def z42 : ZID := ⟨"Z42", by decide⟩
def z99 : ZID := ⟨"Z99", by decide⟩
def z881 : ZID := ⟨"Z881", by decide⟩
def z12427 : ZID := ⟨"Z12427", by decide⟩
def z13518 : ZID := ⟨"Z13518", by decide⟩

end IDs

namespace Keys

def k1 : Key := ⟨"K1", by decide⟩
def k2 : Key := ⟨"K2", by decide⟩
def z1k1 : Key := ⟨"Z1K1", by decide⟩
def z4k1 : Key := ⟨"Z4K1", by decide⟩
def z6k1 : Key := ⟨"Z6K1", by decide⟩
def z7k1 : Key := ⟨"Z7K1", by decide⟩
def z8k5 : Key := ⟨"Z8K5", by decide⟩
def z9k1 : Key := ⟨"Z9K1", by decide⟩
def z14k1 : Key := ⟨"Z14K1", by decide⟩
def z14k2 : Key := ⟨"Z14K2", by decide⟩
def z14k3 : Key := ⟨"Z14K3", by decide⟩
def z14k4 : Key := ⟨"Z14K4", by decide⟩
def z16k1 : Key := ⟨"Z16K1", by decide⟩
def z16k2 : Key := ⟨"Z16K2", by decide⟩
def z18k1 : Key := ⟨"Z18K1", by decide⟩
def z22k1 : Key := ⟨"Z22K1", by decide⟩
def z22k2 : Key := ⟨"Z22K2", by decide⟩
def z40k1 : Key := ⟨"Z40K1", by decide⟩
def z99k1 : Key := ⟨"Z99K1", by decide⟩
def z881k1 : Key := ⟨"Z881K1", by decide⟩
def z12427k1 : Key := ⟨"Z12427K1", by decide⟩
def z13518k1 : Key := ⟨"Z13518K1", by decide⟩

end Keys

/-! ## Lossless raw syntax -/

/-- Lossless JSON-shaped syntax at the trust boundary.

Object order and duplicate keys are preserved.  Numbers retain their source spelling, avoiding
an accidental normalization before validation.  Wikifunctions serializers emit only strings,
arrays, and objects, but quotes can faithfully carry any JSON value. -/
inductive Raw where
  | string : String → Raw
  | number : String → Raw
  | boolean : Bool → Raw
  | null : Raw
  | array : List Raw → Raw
  | object : List (String × Raw) → Raw
deriving Repr

/-! ## Semantic values -/

/-- A semantic Wikifunctions value.

`object type fields` stores `Z1K1` separately, so duplicate or missing type keys are impossible
in this layer.  The normal serializer reintroduces `Z1K1` on the wire. -/
inductive ZObject where
  | string : String → ZObject
  | reference : ZID → ZObject
  | object : ZObject → List (Key × ZObject) → ZObject
  | list : ZObject → List ZObject → ZObject
  | quote : Raw → ZObject
deriving Repr

namespace ZObject

/-- The explicit ZObject type of a value. -/
def typeOf : ZObject → ZObject
  | .string _ => .reference IDs.z6
  | .reference _ => .reference IDs.z9
  | .object type _ => type
  | .list elementType _ =>
      .object (.reference IDs.z7)
        [(Keys.z7k1, .reference IDs.z881), (Keys.z881k1, elementType)]
  | .quote _ => .reference IDs.z99

/-- The data fields of an ordinary object. -/
def fields : ZObject → List (Key × ZObject)
  | .object _ fields => fields
  | _ => []

/-- Look up an ordinary object's data field. -/
def get? (z : ZObject) (key : Key) : Option ZObject :=
  (z.fields.find? (·.1 == key)).map (·.2)

/-- The string payload of a terminal value. -/
def stringValue? : ZObject → Option String
  | .string value => some value
  | _ => none

/-- The referenced ZID of a terminal value. -/
def referenceId? : ZObject → Option ZID
  | .reference zid => some zid
  | _ => none

/-- Boolean key uniqueness, used by structural validation and schemas. -/
def keysNoDup : List Key → Bool
  | [] => true
  | key :: keys => !keys.contains key && keysNoDup keys

mutual
  /-- Representation-level validity, before resolving types or running Z4 validators. -/
  def structurallyValid : ZObject → Bool
    | .string _ => true
    | .reference _ => true
    | .object type fields =>
        structurallyValid type &&
          keysNoDup (fields.map (·.1)) &&
          !(fields.map (·.1)).contains Keys.z1k1 &&
          structurallyValidFields fields
    | .list elementType items =>
        structurallyValid elementType && structurallyValidList items
    | .quote _ => true
  /-- Structural validity of object fields. -/
  def structurallyValidFields : List (Key × ZObject) → Bool
    | [] => true
    | (_, value) :: fields => structurallyValid value && structurallyValidFields fields
  /-- Structural validity of homogeneous list contents. -/
  def structurallyValidList : List ZObject → Bool
    | [] => true
    | value :: values => structurallyValid value && structurallyValidList values
end

/-- Proposition-valued structural validity.  Type validity is a separate registry judgement. -/
def StructurallyValid (z : ZObject) : Prop := z.structurallyValid = true

instance (z : ZObject) : Decidable z.StructurallyValid := by
  unfold StructurallyValid
  infer_instance

@[simp]
theorem structurallyValid_string (value : String) :
    structurallyValid (.string value) = true := rfl

@[simp]
theorem structurallyValid_reference (zid : ZID) :
    structurallyValid (.reference zid) = true := rfl

/-- Quotation is a validation boundary: its payload may be schema-invalid and is not traversed. -/
@[simp]
theorem structurallyValid_quote (payload : Raw) :
    structurallyValid (.quote payload) = true := rfl

end ZObject
end Wikifunctions.Model
