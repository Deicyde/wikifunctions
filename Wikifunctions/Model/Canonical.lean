import Wikifunctions.Model.ZObject

/-!
# Canonical form and the `canonicalize` / `normalize` conversions

`ZObject` (`Model/ZObject.lean`) is the spec's **normal form** — the uniform, evaluator-facing
representation where every value is a node and lists are cons-lists. This module adds the compact
**canonical form** (§Canonical form) — "In order to make ZObjects more readable and more compact,
we usually store and transmit them in the so-called canonical form" — as a *separate* type, with
total conversions both ways.

Canonical form applies exactly three collapses (§Canonical form):
* `Z6`/String  → a bare JSON string;
* `Z9`/Reference → a bare JSON string (its ZID);
* `Z881`/Typed list → a **Benjamin array**: a JSON array whose *first element is the element
  type* and whose remaining elements are the items.

So a canonical value is just JSON: a string, an array, or an object. The two directions are
`canonicalize : ZObject → Canonical` and `normalize : Canonical → ZObject`.
-/

namespace Wikifunctions.Model

/-- A value in **canonical form**: the compact JSON serialization. A string (a bare `Z6` value or
    a bare `Z9` ZID), an `arr` (a Benjamin array for a `Z881` list), or an `obj`. -/
inductive Canonical where
  | str : String → Canonical
  | arr : List Canonical → Canonical
  | obj : List (Key × Canonical) → Canonical
deriving Repr

/- Decidable equality, hand-written (nested-`List` recursion, as for `ZObject`). -/
mutual
  protected def Canonical.decEq : (a b : Canonical) → Decidable (a = b)
    | .str s, .str t =>
        if h : s = t then isTrue (by rw [h]) else isFalse (fun he => by injection he with h'; exact h h')
    | .arr x, .arr y =>
        match Canonical.decEqArr x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun he => by injection he with h'; exact h h')
    | .obj x, .obj y =>
        match Canonical.decEqObj x y with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun he => by injection he with h'; exact h h')
    | .str _, .arr _ => isFalse (fun he => Canonical.noConfusion he)
    | .str _, .obj _ => isFalse (fun he => Canonical.noConfusion he)
    | .arr _, .str _ => isFalse (fun he => Canonical.noConfusion he)
    | .arr _, .obj _ => isFalse (fun he => Canonical.noConfusion he)
    | .obj _, .str _ => isFalse (fun he => Canonical.noConfusion he)
    | .obj _, .arr _ => isFalse (fun he => Canonical.noConfusion he)
  protected def Canonical.decEqArr : (x y : List Canonical) → Decidable (x = y)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun he => by simp at he)
    | _ :: _, [] => isFalse (fun he => by simp at he)
    | a :: x, b :: y =>
        match Canonical.decEq a b with
        | isTrue hab =>
          match Canonical.decEqArr x y with
          | isTrue hxy => isTrue (by rw [hab, hxy])
          | isFalse hxy => isFalse (fun he => by injection he with _ h'; exact hxy h')
        | isFalse hab => isFalse (fun he => by injection he with h' _; exact hab h')
  protected def Canonical.decEqObj : (x y : List (Key × Canonical)) → Decidable (x = y)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun he => by simp at he)
    | _ :: _, [] => isFalse (fun he => by simp at he)
    | (k, v) :: x, (k', v') :: y =>
        if hk : k = k' then
          match Canonical.decEq v v' with
          | isTrue hv =>
            match Canonical.decEqObj x y with
            | isTrue ht => isTrue (by rw [hk, hv, ht])
            | isFalse ht => isFalse (fun he => by injection he with _ ht'; exact ht ht')
          | isFalse hv => isFalse (fun he => by injection he with hh _; injection hh with _ hv'; exact hv hv')
        else isFalse (fun he => by injection he with hh _; injection hh with hk' _; exact hk hk')
end

instance : DecidableEq Canonical := Canonical.decEq

namespace Canonical
open ZObject

/-! ### normal → canonical

`canonicalize` flattens a `Z881` cons-list into a Benjamin array, which forces well-founded
recursion (on `sizeOf`) rather than structural — so it does not reduce in the kernel, and the
checks that run it below are discharged by `native_decide`. -/

mutual
  /-- Convert a normal-form `ZObject` to its compact canonical form. Terminates on `sizeOf`: every
      recursive call is on a structural subterm (list-flattening recurses into the cons tail). -/
  def canonicalize (z : ZObject) : Canonical :=
    match z with
    | .str s => .str s
    -- Z9/Reference → bare ZID
    | .node [("Z1K1", .str "Z9"), ("Z9K1", .str zid)] => .str zid
    -- Z6/String → bare string, unless the value looks like a ZID (kept expanded to stay
    -- distinguishable from a reference)
    | .node [("Z1K1", .str "Z6"), ("Z6K1", .str s)] =>
        if isZID s then .obj [("Z1K1", .str "Z6"), ("Z6K1", .str s)] else .str s
    -- Z881 cons cell → Benjamin array [elemType, item₀, item₁, …]
    | .node [("Z1K1", .node [_, _, ("Z881K1", e)]), ("K1", h), ("K2", tl)] =>
        .arr (canonicalize e :: canonicalize h :: canonTail tl)
    -- empty Z881 list → [elemType]
    | .node [("Z1K1", .node [_, _, ("Z881K1", e)])] => .arr [canonicalize e]
    | .node kvs => .obj (canonObj kvs)
  termination_by sizeOf z
  /-- Flatten the remaining cons cells of a list into their canonical items. -/
  def canonTail (z : ZObject) : List Canonical :=
    match z with
    | .node [("Z1K1", _), ("K1", h), ("K2", tl)] => canonicalize h :: canonTail tl
    | _ => []
  termination_by sizeOf z
  /-- Canonicalize a node's entries. -/
  def canonObj (kvs : List (Key × ZObject)) : List (Key × Canonical) :=
    match kvs with
    | [] => []
    | (k, v) :: rest => (k, canonicalize v) :: canonObj rest
  termination_by sizeOf kvs
end

/-! ### canonical → normal

`normalize` is structurally recursive on the `Canonical` value. A bare string becomes a `Z9`
reference if it is a ZID, else a `Z6` string; a Benjamin array becomes a `Z881` cons-list whose
element type is its first element. -/

mutual
  /-- Convert a canonical value to its normal-form `ZObject`. -/
  def normalize : Canonical → ZObject
    | .str s => if isZID s then reference s else string s
    | .arr [] => emptyList (reference "Z1")                    -- degenerate; an array is never truly empty
    | .arr (t :: items) => typedList (normalize t) (normalizeItems items)
    | .obj kvs => .node (normalizeObj kvs)
  def normalizeItems : List Canonical → List ZObject
    | [] => []
    | c :: cs => normalize c :: normalizeItems cs
  def normalizeObj : List (Key × Canonical) → List (Key × ZObject)
    | [] => []
    | (k, c) :: rest => (k, normalize c) :: normalizeObj rest
end

/-! ### Faithfulness checks -/

-- `normalize` is structural, so its checks hold by `rfl`; `canonicalize` is well-founded (see
-- the note below), so its checks use `native_decide`.
example : normalize (.str "hello") = string "hello"   := rfl
example : normalize (.str "Z40")   = reference "Z40"  := rfl   -- a ZID-shaped string is a reference
example : canonicalize (string "hello")   = .str "hello" := by native_decide
example : canonicalize (reference "Z40")  = .str "Z40"   := by native_decide
-- A Z6 string whose value is ZID-shaped stays expanded, so it can't be confused with a reference.
example : canonicalize (string "Z40") = .obj [("Z1K1", .str "Z6"), ("Z6K1", .str "Z40")] := by native_decide

-- `canonicalize` is well-founded (the list-flattening forces it), so it does not reduce in the
-- kernel; the checks that run it are discharged by `native_decide` (compiler evaluation). This
-- axiom (`Lean.ofReduceBool`) is confined to these example lemmas — the definitions are clean.

-- The number 2: normal object ⟷ canonical `{Z1K1:"Z10", Z10K1:"2"}`.
example : canonicalize natTwo = .obj [("Z1K1", .str "Z10"), ("Z10K1", .str "2")] := by native_decide

-- Lists: a cons-list ⟷ its Benjamin array `["Z6","a","b"]`.
example : canonicalize (typedList (reference "Z6") [string "a", string "b"])
        = .arr [.str "Z6", .str "a", .str "b"] := by native_decide
example : normalize (.arr [.str "Z6", .str "a", .str "b"])
        = typedList (reference "Z6") [string "a", string "b"] := rfl

-- Round trips (on well-formed inputs).
example : normalize (canonicalize natTwo) = natTwo := by native_decide
example : normalize (canonicalize (typedList (reference "Z6") [string "a", string "b"]))
        = typedList (reference "Z6") [string "a", string "b"] := by native_decide
example : canonicalize (normalize (.arr [.str "Z6", .str "a", .str "b"]))
        = .arr [.str "Z6", .str "a", .str "b"] := by native_decide

end Canonical
end Wikifunctions.Model
