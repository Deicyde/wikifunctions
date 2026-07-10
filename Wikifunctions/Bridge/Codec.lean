import Wikifunctions.Model.Schema

/-!
# Proof-carrying ZObject codecs

A `Codec` records the executable boundary between a Lean type and semantic ZObjects.  It carries
an executable type schema, proofs that encodings satisfy it, an encoder/decoder round trip, and
canonicality of every successfully decoded object.
-/

namespace Wikifunctions.Bridge

open Model

/-- A total encoder and partial decoder for semantic ZObjects. -/
structure Codec (α : Type) where
  /-- Encode a Lean value as a semantic ZObject. -/
  encode : α → ZObject
  /-- Decode a semantic ZObject when it belongs to this codec's accepted representation. -/
  decode : ZObject → Option α
  /-- Revision-pinned executable type constraint for this representation. -/
  schema : Schema.Checked
  /-- Every encoded value satisfies the declared type schema at its explicit fuel bound. -/
  encode_schemaValid : ∀ value, schema.Valid (encode value)
  /-- Values produced by the encoder satisfy representation-level validity. -/
  encode_structurallyValid : ∀ value, (encode value).StructurallyValid
  /-- Decoding a freshly encoded value recovers that value. -/
  decode_encode : ∀ value, decode (encode value) = some value
  /-- Every successfully decoded object is the canonical encoding of the decoded value. -/
  encode_of_decode_eq_some :
    ∀ {object value}, decode object = some value → encode value = object

namespace Codec

/-- Every proof-carrying codec has an injective encoder. -/
theorem encode_injective (codec : Codec α) : Function.Injective codec.encode := by
  intro left right h
  have decoded : codec.decode (codec.encode left) = codec.decode (codec.encode right) :=
    congrArg codec.decode h
  apply Option.some.inj
  simpa only [codec.decode_encode] using decoded

/-- A decoder succeeds exactly on the canonical image of its encoder. -/
theorem decode_eq_some_iff (codec : Codec α) {object : ZObject} {value : α} :
    codec.decode object = some value ↔ codec.encode value = object := by
  constructor
  · exact codec.encode_of_decode_eq_some
  · intro h
    rw [← h]
    exact codec.decode_encode value

end Codec
end Wikifunctions.Bridge
