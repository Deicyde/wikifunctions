/-!
# `Z1`/ZObjects — the ground of the Wikifunctions model (normal form)

Every Wikifunctions value is a `ZObject`, modelled here in the spec's **normal form**
(§Normal form). Normal form is *uniform*: every ZObject is a node of key/value pairs, and the
only leaf is a raw string — the value inside a `Z6`/String or `Z9`/Reference terminal, or a type
tag. The spec singles this form out as the evaluator's input:

> "For the processing of ZObjects by the evaluator, all ZObjects are turned into the normal form
>  described above. ... Normal forms are used as inputs for the evaluation engine. They ensure
>  that the input for evaluation is always uniform and easy to process, and that it requires a
>  minimal amount of special cases."

A key consequence, stated by the spec, is that **"all Lists are represented as ZObjects, not as
arrays"**: a `Z881`/Typed list is a cons-list of nodes (head `K1`, tail `K2`), so it needs no
special constructor here — it is just a shape of `node`. The compact **canonical form** (bare
terminals + Benjamin arrays), which is what we store and transmit, is a *separate* type with
`canonicalize` / `normalize` conversions; see `Wikifunctions/Model/Canonical.lean`.

Grounded in the Function model, §Z1/ZObjects and §Normal form
<https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Normal_form>. This module is
Mathlib-free.
-/

namespace Wikifunctions.Model

/-- A key on a ZObject (§Z3/Keys): `K` + a positive natural, optionally ZID-prefixed. -/
abbrev Key := String

/-- `Z1`/Object — the universal type. **Every Wikifunctions value is a `ZObject`.**

    Normal form: a `ZObject` is either a raw `str` leaf (only ever the payload of a `Z6`/`Z9`
    terminal or a type tag) or a `node` — an ordered list of key/value pairs. Two constructors;
    every "type" (`Z6`, `Z9`, `Z4`, `Z8`, `Z7`, `Z881` lists, …) is a shape of `node`. -/
inductive ZObject where
  /-- A raw string leaf: the value of a `Z6K1`/`Z9K1` payload or a type-tag name. -/
  | str  : String → ZObject
  /-- A ZObject as an ordered list of key/value pairs (§Z1/ZObjects). -/
  | node : List (Key × ZObject) → ZObject
deriving Repr

/- Decidable equality, hand-written: the built-in `deriving DecidableEq` handler does not support
   this nested inductive (the recursive occurrence sits under `List (Key × ·)`). -/
mutual
  protected def ZObject.decEq : (a b : ZObject) → Decidable (a = b)
    | .str s, .str t =>
        if h : s = t then isTrue (by rw [h]) else isFalse (fun he => by injection he with h'; exact h h')
    | .node x, .node y =>
        match ZObject.decEqEntries x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun he => by injection he with h'; exact h h')
    | .str _,  .node _ => isFalse (fun he => ZObject.noConfusion he)
    | .node _, .str _  => isFalse (fun he => ZObject.noConfusion he)
  protected def ZObject.decEqEntries : (x y : List (Key × ZObject)) → Decidable (x = y)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun he => by simp at he)
    | _ :: _, [] => isFalse (fun he => by simp at he)
    | (k, v) :: x, (k', v') :: y =>
        if hk : k = k' then
          match ZObject.decEq v v' with
          | isTrue hv =>
            match ZObject.decEqEntries x y with
            | isTrue ht => isTrue (by rw [hk, hv, ht])
            | isFalse ht => isFalse (fun he => by injection he with _ ht'; exact ht ht')
          | isFalse hv => isFalse (fun he => by injection he with hh _; injection hh with _ hv'; exact hv hv')
        else isFalse (fun he => by injection he with hh _; injection hh with hk' _; exact hk hk')
end

instance : DecidableEq ZObject := ZObject.decEq

namespace ZObject

/-! ### Accessors -/

/-- The key/value pairs of a ZObject (empty for a `str` leaf). -/
def entries : ZObject → List (Key × ZObject)
  | node kvs => kvs
  | _        => []

/-- The keys present on a ZObject, in order. -/
def keys (z : ZObject) : List Key := z.entries.map (·.1)

/-- Key lookup: the value at key `k`, or `none`. First occurrence wins. -/
def get? (z : ZObject) (k : Key) : Option ZObject :=
  (z.entries.find? (·.1 == k)).map (·.2)

/-- The `Z1K1`/type value of a node. -/
def type? (z : ZObject) : Option ZObject := z.get? "Z1K1"

/-- Is `s` a ZID — `Z` followed by one or more digits (§Z9/Reference)? -/
def isZID (s : String) : Bool :=
  match s.toList with
  | 'Z' :: d :: rest => (d :: rest).all Char.isDigit
  | _ => false

/-! ### Terminals as smart constructors (normal form)

A `Z6`/String and a `Z9`/Reference are two-key nodes whose payloads bottom out in raw `str`
leaves. Their own `Z1K1` tag is the bare string `"Z6"`/`"Z9"` (the base case that stops the
type-tag regress); every *other* object tags its `Z1K1` with a `reference` node. -/

/-- `Z6`/String: `{Z1K1: "Z6", Z6K1: s}`. -/
def string (s : String) : ZObject := node [("Z1K1", str "Z6"), ("Z6K1", str s)]

/-- `Z9`/Reference: `{Z1K1: "Z9", Z9K1: zid}`. -/
def reference (zid : String) : ZObject := node [("Z1K1", str "Z9"), ("Z9K1", str zid)]

/-- The `Z6`/String value, if `z` is one. -/
def stringValue? (z : ZObject) : Option String :=
  match z.get? "Z1K1", z.get? "Z6K1" with
  | some (str "Z6"), some (str s) => some s
  | _, _ => none

/-- The referenced ZID, if `z` is a `Z9`/Reference. -/
def referenceId? (z : ZObject) : Option String :=
  match z.get? "Z1K1", z.get? "Z9K1" with
  | some (str "Z9"), some (str zid) => some zid
  | _, _ => none

def isString    (z : ZObject) : Bool := z.stringValue?.isSome
def isReference (z : ZObject) : Bool := z.referenceId?.isSome

/-- The ZID naming a ZObject's type. A terminal tags `Z1K1` with a bare string (`"Z6"`/`"Z9"`);
    every other object tags it with a `reference` node, whose ZID is the type. -/
def typeId? (z : ZObject) : Option String :=
  match z.get? "Z1K1" with
  | some (str s)  => some s                 -- terminal base case: the bare type name
  | some tagNode  => tagNode.referenceId?   -- object: Z1K1 is a Z9 reference to the type
  | none          => none

/-! ### `Z881`/Typed lists — cons-lists of nodes (§Normal form: "Lists are ZObjects, not arrays")

A typed list's type is a `Z7` call to `Z881` with the element type; each cons cell carries head
`K1` and tail `K2`; the empty list is the type alone. -/

/-- The list type: `{Z1K1: Z7, Z7K1: Z881, Z881K1: elemType}` (fully-expanded normal form). -/
def listType (elemType : ZObject) : ZObject :=
  node [("Z1K1", reference "Z7"), ("Z7K1", reference "Z881"), ("Z881K1", elemType)]

/-- The empty `Z881` list of `elemType`. -/
def emptyList (elemType : ZObject) : ZObject := node [("Z1K1", listType elemType)]

/-- One cons cell: `{Z1K1: listType, K1: head, K2: tail}`. -/
def cons (elemType head tail : ZObject) : ZObject :=
  node [("Z1K1", listType elemType), ("K1", head), ("K2", tail)]

/-- A `Z881` typed list of `elemType` from a Lean list, built as a cons-list of nodes. -/
def typedList (elemType : ZObject) : List ZObject → ZObject
  | []      => emptyList elemType
  | x :: xs => cons elemType x (typedList elemType xs)

/-! ### Faithfulness check: the spec's number 2, in normal form -/

/-- The natural number 2 in normal form: `{Z1K1: <ref Z10>, Z10K1: <str "2">}`. -/
def natTwo : ZObject := node [("Z1K1", reference "Z10"), ("Z10K1", string "2")]

/-- `natTwo` reproduces the spec's §Normal-form example *definitionally*. -/
example : natTwo =
    node [("Z1K1",  node [("Z1K1", str "Z9"), ("Z9K1", str "Z10")]),
          ("Z10K1", node [("Z1K1", str "Z6"), ("Z6K1", str "2")])] := rfl

example : natTwo.typeId?              = some "Z10" := rfl   -- its type is Z10
example : (string "hi").stringValue?  = some "hi"  := rfl
example : (reference "Z40").referenceId? = some "Z40" := rfl
example : (reference "Z40").typeId?   = some "Z9"  := rfl   -- a reference is itself a Z9

/-! ### Well-formedness

Permissive type, decidable validity predicate. A bare `str` is not a standalone ZObject. A node
is well-formed if it is a `Z6`/`Z9` terminal shape (payload a raw string) or a general object:
a `Z1K1` key, no duplicate keys, and every value well-formed. -/

def keysNoDup : List Key → Bool
  | [] => true
  | k :: ks => !ks.contains k && keysNoDup ks

/-- The `Z6`/String terminal shape: exactly `Z1K1 = "Z6"` and `Z6K1` a raw string. -/
def isZ6 (kvs : List (Key × ZObject)) : Bool :=
  kvs.length == 2 &&
  (match (node kvs).get? "Z1K1" with | some (str "Z6") => true | _ => false) &&
  (match (node kvs).get? "Z6K1" with | some (str _)    => true | _ => false)

/-- The `Z9`/Reference terminal shape: exactly `Z1K1 = "Z9"` and `Z9K1` a raw string. -/
def isZ9 (kvs : List (Key × ZObject)) : Bool :=
  kvs.length == 2 &&
  (match (node kvs).get? "Z1K1" with | some (str "Z9") => true | _ => false) &&
  (match (node kvs).get? "Z9K1" with | some (str _)    => true | _ => false)

mutual
  def wf : ZObject → Bool
    | str _ => false
    | node kvs =>
        isZ6 kvs || isZ9 kvs ||
        ((kvs.any (·.1 == "Z1K1")) && keysNoDup (kvs.map (·.1)) && wfEntries kvs)
  def wfEntries : List (Key × ZObject) → Bool
    | [] => true
    | (_, v) :: rest => wf v && wfEntries rest
end

/-- A ZObject is well-formed. -/
def WellFormed (z : ZObject) : Prop := wf z = true

instance (z : ZObject) : Decidable z.WellFormed := by unfold WellFormed; infer_instance

example : wf natTwo = true := by decide
example : wf (string "anything") = true := by decide
example : wf (reference "Z13701") = true := by decide
example : wf (str "bare") = false := by decide                            -- a bare string is not a ZObject
example : wf (typedList (reference "Z6") [string "a", string "b"]) = true := by decide  -- a list is well-formed
example : wf (node [("Z10K1", string "2")]) = false := by decide          -- no Z1K1

end ZObject
end Wikifunctions.Model
