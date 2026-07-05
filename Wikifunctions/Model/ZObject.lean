/-!
# `Z1`/ZObjects — the ground of the Wikifunctions model

Every Wikifunctions value is a `ZObject`, modelled here in the spec's **canonical form**
(§Canonical form): the two terminal types are *atomic leaves* — a `Z6`/String is a bare string,
a `Z9`/Reference is a bare ZID — and everything else is a `node`, an ordered list of key/value
pairs. This mirrors what the live API returns (references appear as bare ZIDs) and keeps
references — the thing an evaluator *resolves* — a first-class, distinguishable constructor.

Grounded in the Function model, §Z1/ZObjects
<https://www.wikifunctions.org/wiki/Wikifunctions:Function_model#Z1/ZObjects>:

> "A ZObject consists of a list of Key/value pairs. Every value in a Key/value pair is a
>  ZObject. ... Z6/String and Z9/Reference are called terminal values. They don't expand
>  further. A Z6/String has ... Z6K1/string value, with an arbitrary string. A Z9/Reference
>  has ... Z9K1/reference ID, with a string representing a ZID. Every Key can only appear once
>  on each ZObject."

and §Canonical form, where a `Z6`/String canonicalises to its bare string and a `Z9`/Reference to
its bare ZID. So a ZObject is inductively a `str` (Z6/String), a `ref` (Z9/Reference), or a
`node`. Everything else in the model (`Z4`/Types, `Z8`/Functions, `Z7`/calls) is a shape of
`node`. This module is Mathlib-free.
-/

namespace Wikifunctions.Model

/-- A key on a ZObject. Per §Z3/Keys a key is `K` followed by a positive natural, optionally
    preceded by a ZID (a *global* key like `Z7K1`, or a *local* key like `K1`). -/
abbrev Key := String

/-- `Z1`/Object — the universal type. **Every Wikifunctions value is a `ZObject`.**

    Canonical form: the two terminals are atomic (`str` a `Z6`/String, `ref` a `Z9`/Reference),
    and a `node` is an ordered list of key/value pairs whose values are ZObjects. Order is
    significant (the spec says *list*); key uniqueness is an invariant, captured by `WellFormed`. -/
inductive ZObject where
  /-- A `Z6`/String, atomically: its arbitrary string value. -/
  | str  : String → ZObject
  /-- A `Z9`/Reference, atomically: the ZID it names. Distinct from `str` — a reference is
      resolved, a string is a literal — even when the underlying text coincides. -/
  | ref  : String → ZObject
  /-- A ZObject as an ordered list of key/value pairs (§Z1/ZObjects). -/
  | node : List (Key × ZObject) → ZObject
deriving Repr

/- Decidable equality, hand-written: the built-in `deriving DecidableEq` handler does not
   support this nested inductive (the recursive occurrence sits under `List (Key × ·)`), so we
   recurse mutually over `ZObject` and its entry list. -/
mutual
  protected def ZObject.decEq : (a b : ZObject) → Decidable (a = b)
    | .str s, .str t =>
        if h : s = t then isTrue (by rw [h]) else isFalse (fun he => by injection he with h'; exact h h')
    | .ref s, .ref t =>
        if h : s = t then isTrue (by rw [h]) else isFalse (fun he => by injection he with h'; exact h h')
    | .node x, .node y =>
        match ZObject.decEqEntries x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun he => by injection he with h'; exact h h')
    | .str _,  .ref _  => isFalse (fun he => ZObject.noConfusion he)
    | .str _,  .node _ => isFalse (fun he => ZObject.noConfusion he)
    | .ref _,  .str _  => isFalse (fun he => ZObject.noConfusion he)
    | .ref _,  .node _ => isFalse (fun he => ZObject.noConfusion he)
    | .node _, .str _  => isFalse (fun he => ZObject.noConfusion he)
    | .node _, .ref _  => isFalse (fun he => ZObject.noConfusion he)
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
  | _        => []

/-- The keys present on a ZObject, in order. -/
def keys (z : ZObject) : List Key := z.entries.map (·.1)

/-- Key lookup: the value at key `k`, or `none`. First occurrence wins (unambiguous on a
    well-formed ZObject, where a key appears at most once). -/
def get? (z : ZObject) (k : Key) : Option ZObject :=
  (z.entries.find? (·.1 == k)).map (·.2)

/-- The ZID naming a ZObject's type: a `str` is a `Z6`, a `ref` is a `Z9`, and a `node`'s type
    is the ZID its `Z1K1` reference names (§Z1/ZObjects: "every ZObject must have a key
    Z1K1/type"). `none` for a node without a `Z1K1` reference. -/
def typeId? : ZObject → Option String
  | str _   => some "Z6"
  | ref _   => some "Z9"
  | node kvs => match (kvs.find? (·.1 == "Z1K1")).map (·.2) with
                | some (ref zid) => some zid
                | _              => none

/-- The `Z1K1`/type value of a node (a terminal has no keys). -/
def type? (z : ZObject) : Option ZObject := z.get? "Z1K1"

/-! ### Terminal recognizers -/

def isString    : ZObject → Bool | str _ => true | _ => false
def isReference : ZObject → Bool | ref _ => true | _ => false

/-- The string value of a `Z6`/String, if it is one. -/
def stringValue? : ZObject → Option String | str s => some s | _ => none
/-- The referenced ZID of a `Z9`/Reference, if it is one. -/
def referenceId? : ZObject → Option String | ref z => some z | _ => none

/-! ### Faithfulness check: the spec's number 2, in canonical form

§Normal form shows the natural number 2 as `{Z1K1:{Z1K1:Z9,Z9K1:Z10}, Z10K1:{Z1K1:Z6,Z6K1:"2"}}`;
its canonical form (§Canonical form) collapses the terminals to `{Z1K1: Z10, Z10K1: "2"}` — the
`Z10` a reference, the `"2"` a string. That is exactly what our canonical `natTwo` is. (`Z10` was
the natural-number type in the spec's example; the structure is the point.) -/

/-- The natural number 2, in canonical form. -/
def natTwo : ZObject := node [("Z1K1", ref "Z10"), ("Z10K1", str "2")]

example : natTwo.get? "Z1K1"  = some (ref "Z10") := rfl   -- its type key is the reference Z10
example : natTwo.get? "Z10K1" = some (str "2")   := rfl   -- its value key is the string "2"
example : natTwo.typeId?      = some "Z10"        := rfl   -- so its type is Z10
example : (str "hello").stringValue?    = some "hello"   := rfl
example : (ref "Z13701").referenceId?   = some "Z13701"  := rfl
example : str "a" ≠ str "b" := by decide                  -- the hand-written DecidableEq computes
example : str "Z10" ≠ ref "Z10" := by decide              -- a string literal is NOT a reference

/-! ### Well-formedness

The inductive is permissive (as the dynamically-typed deployed system is); validity is a
*separate, decidable* predicate. A terminal is well-formed — a `str` is any `Z6`/String, a `ref`
is a `Z9`/Reference iff its payload is a ZID (§Z9: "a string representing a ZID"). A `node` must
carry a `Z1K1` key, have no duplicate keys (§Z1/ZObjects: "every Key can only appear once"), and
have every value well-formed. -/

/-- Boolean "no duplicate keys" (kept Mathlib-free). -/
def keysNoDup : List Key → Bool
  | [] => true
  | k :: ks => !ks.contains k && keysNoDup ks

/-- Is `s` a ZID — `Z` followed by one or more digits (§Z9/Reference)? -/
def isZID (s : String) : Bool :=
  match s.toList with
  | 'Z' :: d :: rest => (d :: rest).all Char.isDigit
  | _ => false

mutual
  def wf : ZObject → Bool
    | str _   => true
    | ref zid => isZID zid
    | node kvs => (kvs.any (·.1 == "Z1K1")) && keysNoDup (kvs.map (·.1)) && wfEntries kvs
  def wfEntries : List (Key × ZObject) → Bool
    | [] => true
    | (_, v) :: rest => wf v && wfEntries rest
end

/-- A ZObject is well-formed. -/
def WellFormed (z : ZObject) : Prop := wf z = true

instance (z : ZObject) : Decidable z.WellFormed := by unfold WellFormed; infer_instance

example : wf natTwo = true := by decide
example : wf (str "anything") = true := by decide
example : wf (ref "Z13701") = true := by decide
example : wf (ref "notAZID") = false := by decide                    -- a reference must name a ZID
example : wf (node [("Z10K1", str "2")]) = false := by decide        -- no Z1K1
example : wf (node [("Z1K1", ref "Z6"), ("Z1K1", str "b")]) = false := by decide  -- duplicate key

end ZObject
end Wikifunctions.Model
