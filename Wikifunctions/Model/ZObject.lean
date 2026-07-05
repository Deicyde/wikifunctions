/-!
# `Z1`/ZObjects — the ground of the Wikifunctions model

A from-the-spec rebuild of the formalization. Where the previous development started from a
typed value universe (`Val`), this starts where the spec does: **every Wikifunctions value is
a `ZObject`**, and `ZObject` is a single inductive type.

Grounded verbatim in the Function model, §Z1/ZObjects
<https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z1/ZObjects>:

> "A ZObject consists of a list of Key/value pairs. Every value in a Key/value pair is a
>  ZObject. Values can be either a Z6/String, a Z9/Reference, or have any other type.
>  Z6/String and Z9/Reference are called terminal values. They don't expand further.
>  A Z6/String has exactly two keys, Z1K1/type with the value 'Z6', and Z6K1/string value,
>  with an arbitrary string. A Z9/Reference has exactly two keys, Z1K1/type with the value
>  'Z9', and Z9K1/reference ID, with a string representing a ZID. Every Key can only appear
>  once on each ZObject. ... Every ZObject must have a key Z1K1/type."

and §Normal form:

> "the normal form of a ZObject is a tree where all leaves are either of the type Z6/String
>  or Z9/Reference. ... all Lists are represented as ZObjects, not as arrays."

Reading that literally: a ZObject is inductively either a **terminal string leaf** (the
arbitrary string a `Z6K1` carries, or the ZID a `Z9K1` carries — these "don't expand
further") or a **node**: an ordered list of key/value pairs whose values are ZObjects. Two
constructors, no more. Everything else in the model (`Z4`/Types, `Z8`/Functions, `Z7`/calls,
`Z881`/lists) is a particular shape of `node`. `natTwo` below reproduces the spec's own
normal-form example by `rfl`.

This module is deliberately Mathlib-free: it is pure syntax, the substrate the rest of the
rebuild will sit on.
-/

namespace Wikifunctions.Model

/-- A key on a ZObject. Per §Z3/Keys a key is `K` followed by a positive natural, optionally
    preceded by a ZID: a *global* key like `Z7K1` (a named argument) or a *local* key like
    `K1` (a positional argument). Modelled as the raw key string. -/
abbrev Key := String

/-- `Z1`/Object — the universal type. **Every Wikifunctions value is a `ZObject`.**

    Per §Z1/ZObjects a ZObject is a list of key/value pairs whose values are ZObjects,
    bottoming out in the two *terminal* types (`Z6`/String, `Z9`/Reference), which carry a
    raw string and do not expand further. Hence two constructors: a terminal string leaf and
    a node. Order is significant (the spec says *list*, not set); uniqueness of keys is an
    invariant, captured by `WellFormed` rather than by the type. -/
inductive ZObject where
  /-- A terminal string leaf: the arbitrary string value carried by a `Z6K1`, the ZID carried
      by a `Z9K1`, or a terminal type tag (`"Z6"`/`"Z9"`) on `Z1K1`. It "doesn't expand
      further" (§Z1/ZObjects). In normal form a bare leaf only ever appears as such a value. -/
  | str : String → ZObject
  /-- A ZObject as an ordered list of key/value pairs (§Z1/ZObjects: "a list of Key/value
      pairs. Every value in a Key/value pair is a ZObject"). -/
  | node : List (Key × ZObject) → ZObject
deriving Repr

/- Decidable equality, hand-written: the built-in `deriving DecidableEq` handler does not
   support this nested inductive (the recursive occurrence sits under `List (Key × ·)`), so
   we recurse mutually over `ZObject` and its entry list. -/
mutual
  protected def ZObject.decEq : (a b : ZObject) → Decidable (a = b)
    | .str s, .str t =>
        if h : s = t then isTrue (by rw [h]) else isFalse (fun he => by injection he with h'; exact h h')
    | .node x, .node y =>
        match ZObject.decEqEntries x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun he => by injection he with h'; exact h h')
    | .str _, .node _ => isFalse (fun he => ZObject.noConfusion he)
    | .node _, .str _ => isFalse (fun he => ZObject.noConfusion he)
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

/-- The key/value pairs of a ZObject (empty for a terminal leaf). -/
def entries : ZObject → List (Key × ZObject)
  | node kvs => kvs
  | str _ => []

/-- The keys present on a ZObject, in order. -/
def keys (z : ZObject) : List Key := z.entries.map (·.1)

/-- Key lookup: the value at key `k`, or `none`. First occurrence wins (§Z1/ZObjects: a key
    appears at most once on a well-formed ZObject, so first-wins is unambiguous there). -/
def get? (z : ZObject) (k : Key) : Option ZObject :=
  (z.entries.find? (·.1 == k)).map (·.2)

/-- The declared type of a ZObject: the value of its `Z1K1` key. Per §Z1/ZObjects "every
    ZObject must have a key Z1K1/type"; a terminal string leaf has none, so this is `Option`. -/
def type? (z : ZObject) : Option ZObject := z.get? "Z1K1"

/-! ### The two terminal types, as smart constructors (normal form) -/

/-- `Z6`/String — a terminal carrying an arbitrary string: `{Z1K1: Z6, Z6K1: s}`. -/
def string (s : String) : ZObject := node [("Z1K1", str "Z6"), ("Z6K1", str s)]

/-- `Z9`/Reference — a terminal carrying a ZID: `{Z1K1: Z9, Z9K1: zid}`. -/
def reference (zid : String) : ZObject := node [("Z1K1", str "Z9"), ("Z9K1", str zid)]

/-- Is this the `Z6`/String terminal? (`Z1K1` tag is the leaf `"Z6"`.) We match the type tag
    on the underlying *string* rather than compare whole `ZObject`s, so it reduces cleanly. -/
def isString (z : ZObject) : Bool :=
  match z.type? with | some (str "Z6") => true | _ => false

/-- Is this the `Z9`/Reference terminal? (`Z1K1` tag is the leaf `"Z9"`.) -/
def isReference (z : ZObject) : Bool :=
  match z.type? with | some (str "Z9") => true | _ => false

/-- The underlying string of a `Z6`/String (its `Z6K1`), if it is one. -/
def stringValue? (z : ZObject) : Option String :=
  if z.isString then match z.get? "Z6K1" with | some (str s) => some s | _ => none else none

/-- The referenced ZID of a `Z9`/Reference (its `Z9K1`), if it is one. -/
def referenceId? (z : ZObject) : Option String :=
  if z.isReference then match z.get? "Z9K1" with | some (str s) => some s | _ => none else none

/-- The ZID naming a ZObject's type, whether its `Z1K1` tag is a terminal leaf (`"Z6"`/`"Z9"`)
    or a `Z9`/Reference to a `Z4`/Type (the non-terminal case). This is the discriminator the
    generated per-type code checks. -/
def typeId? (z : ZObject) : Option String :=
  match z.type? with
  | some (str s) => some s          -- terminal tag: a bare `"Z6"`/`"Z9"`
  | some v => v.referenceId?        -- non-terminal: a `Z9` reference to the type
  | none => none

/-! ### Faithfulness check: the spec's own §Normal form example

`{Z1K1: {Z1K1: Z9, Z9K1: Z10}, Z10K1: {Z1K1: Z6, Z6K1: "2"}}` — the natural number 2. (The
example predates the current natural-number type; `Z10` was the natural type when it was
written. The *structure* is what we reproduce.) -/

/-- The natural number 2, built from the smart constructors. -/
def natTwo : ZObject := node [("Z1K1", reference "Z10"), ("Z10K1", string "2")]

/-- `natTwo` is *definitionally* the spec's normal-form tree — every leaf a `Z6`/`Z9`. -/
example : natTwo = node
    [ ("Z1K1",  node [("Z1K1", str "Z9"), ("Z9K1", str "Z10")]),
      ("Z10K1", node [("Z1K1", str "Z6"), ("Z6K1", str "2")]) ] := rfl

example : natTwo.type? = some (reference "Z10") := rfl
example : natTwo.get? "Z10K1" = some (string "2") := rfl
example : (string "2").isString = true := by decide
example : (reference "Z10").isReference = true := by decide
example : (string "hello").stringValue? = some "hello" := by decide
example : (reference "Z13701").referenceId? = some "Z13701" := by decide
example : natTwo.keys = ["Z1K1", "Z10K1"] := rfl
example : string "a" ≠ string "b" := by decide          -- the hand-written `DecidableEq` computes

/-! ### Well-formedness (normal form)

The inductive `ZObject` is deliberately permissive — it admits trees the spec would reject (a
bare leaf standing alone, a node with no `Z1K1`, duplicate keys) — because the deployed system
is dynamically typed and its validators can be skipped. Validity is therefore a *separate,
decidable predicate*, matching the spec's validator posture. Per §Z1/ZObjects a well-formed
normal-form ZObject must "have a key Z1K1/type", "every Key can only appear once", and its
leaves must be the two terminals `Z6`/`Z9`. -/

/-- Boolean "no duplicate keys" (kept Mathlib-free). -/
def keysNoDup : List Key → Bool
  | [] => true
  | k :: ks => !ks.contains k && keysNoDup ks

/-- The `Z6`/String terminal shape: exactly `Z1K1 = "Z6"` then `Z6K1 = <string leaf>`. -/
def isZ6Shape : List (Key × ZObject) → Bool
  | [("Z1K1", str "Z6"), ("Z6K1", str _)] => true
  | _ => false

/-- The `Z9`/Reference terminal shape: exactly `Z1K1 = "Z9"` then `Z9K1 = <ZID leaf>`. -/
def isZ9Shape : List (Key × ZObject) → Bool
  | [("Z1K1", str "Z9"), ("Z9K1", str _)] => true
  | _ => false

/- `wf z` — `z` is a well-formed normal-form *value* (§Z1/ZObjects). A bare `str` leaf is not
   a standalone value; a `node` must carry a `Z1K1` key with no duplicate keys, and be either
   a `Z6`/`Z9` terminal (leaves) or have every value itself well-formed. Mutual with
   `wfEntries` because the recursion runs under `List (Key × ·)`. -/
mutual
  def wf : ZObject → Bool
    | str _ => false
    | node kvs =>
        (kvs.any (·.1 == "Z1K1")) && keysNoDup (kvs.map (·.1)) &&
        (isZ6Shape kvs || isZ9Shape kvs || wfEntries kvs)
  def wfEntries : List (Key × ZObject) → Bool
    | [] => true
    | (_, v) :: rest => wf v && wfEntries rest
end

/-- A ZObject is well-formed. -/
def WellFormed (z : ZObject) : Prop := wf z = true

instance (z : ZObject) : Decidable z.WellFormed := by unfold WellFormed; infer_instance

-- The spec's normal-form number 2 is well-formed; so are the terminals.
example : wf natTwo = true := by decide
example : wf (string "x") = true := by decide
example : wf (reference "Z13701") = true := by decide
-- ...and the things the spec rejects are rejected:
example : wf (str "bare") = false := by decide                       -- a bare leaf is not a value
example : wf (node [("Z6K1", str "x")]) = false := by decide         -- no Z1K1
example : wf (node [("Z1K1", reference "Z6"), ("Z1K1", str "b")]) = false := by decide  -- duplicate key

end ZObject
end Wikifunctions.Model
