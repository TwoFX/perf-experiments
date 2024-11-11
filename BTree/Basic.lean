/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Lean.Data.RBMap
import Lean.Elab.Command
import Std.Data.HashMap
-- prelude
-- import Init.Data.Ord
-- import Init.Data.Nat.Linear
-- import Init.Data.Array.Mem
-- import Init.Data.Array.Lemmas
-- import Init.Data.Repr
-- import Init.Core


set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

@[inline]
unsafe def Array.fastInsertAtUnsafe (as : Array α) (i : USize) (a : α) (_hi : i.toNat < as.size) : Array α :=
  unsafeCast <| go (unsafeCast as) i a
where
  @[inline] go (as : Array NonScalar) (i : USize) (a : α) : Array NonScalar :=
    let as := as.push default
    let as := loop as (as.size.toUSize - 1)
    as.uset i (unsafeCast a) lcProof
  loop (as : Array NonScalar) (j : USize) : Array NonScalar :=
    if i < j then
      loop (as.uset j (as.uget (j - 1) lcProof) lcProof) (j - 1)
    else
      as

-- @[implemented_by Array.fastInsertAtUnsafe]
-- def Array.fastInsertAt (as : Array α) (i : USize) (a : α) (hi : i.toNat < as.size) : Array α :=
--   sorry

@[inline]
def Array.fastInsertAt (as : Array α) (i : USize) (a : α) (_hi : i.toNat < as.size) : Array α :=
  Array.insertAtFast as a i.toNat

namespace Lean

@[simp]
theorem Array.size_mkEmpty {c} : (Array.mkEmpty c : Array α).size = 0 := by
  simp [Array.mkEmpty]

@[simp]
theorem Array.size_insertAt {a : Array α} {i x} : (a.insertAt i x).size = a.size + 1 := by
  simp only [Array.insertAt]
  suffices ∀ (a : Array α) i b j, (Array.insertAt.loop a i b j).size = b.size by
    rw [this, Array.size_push]
  intros a i b j
  induction b, j using Array.insertAt.loop.induct a i
  · next as j h j' as' ih =>
    rw [Array.insertAt.loop]
    simp_all [as']
  · next as j ih =>
    rw [Array.insertAt.loop]
    simp [ih]

theorem Array.getElem_insertAt_lt {as : Array α} {i : Fin (as.size + 1)} {a} {j : Nat} {h} (h' : j < i) :
    (as.insertAt i a)[j]'h = as[j]'(by simp at h; omega) := by
  sorry

theorem Array.getElem_insertAt_eq {as : Array α} {i : Fin (as.size + 1)} {a} :
    (as.insertAt i a)[i]'(by simp) = a :=
  sorry

theorem Array.getElem_insertAt_gt {as : Array α} {i : Fin (as.size + 1)} {a} {j : Nat} {h} (h' : i < j) :
    (as.insertAt i a)[j]'h = as[j - 1]'(sorry) := sorry

theorem Array.getElem_insertAt (as : Array α) (i : Fin (as.size + 1)) (a) (j : Nat) (h) :
    (as.insertAt i a)[j]'h = if h₁ : j < i then as[j]'(by simp at h; omega) else
      if h₂ : j = i then a else as[j - 1]'(sorry) := sorry

inductive BTreeNode (α : Type u) (β : Type v) where
  | leaf : Array α → Array β → BTreeNode α β
  | internal : Array α → Array β → Array (BTreeNode α β) → BTreeNode α β

partial def rep [Repr α] [Repr β] (n : BTreeNode α β) : String :=
  match n with
  | .leaf keys values => "(" ++ (reprArg keys |>.pretty) ++ "|" ++ (reprArg values |>.pretty) ++ ")"
  | .internal keys values children => "(" ++ (reprArg keys |>.pretty) ++ "|" ++ (reprArg values |>.pretty)  ++ "|" ++ String.intercalate ", " (children.data.map rep) ++ ")"

instance [Repr α] [Repr β] : Repr (BTreeNode α β) where
  reprPrec a _ := rep a

namespace BTreeNode

@[inline] def dbgTraceIfShared (a : α) (b : β) := b

@[inline] private def b : Nat := 6
@[inline] private def capacity : Nat := 2 * b - 1

@[inline]
def keys : BTreeNode α β → Array α
  | .leaf keys _ => keys
  | .internal keys _ _ => keys

@[inline]
def values : BTreeNode α β → Array β
  | .leaf _ values => values
  | .internal _ values _ => values

@[inline]
def empty (α : Type u) (β : Type v) : BTreeNode α β :=
  .leaf (.mkEmpty (capacity + 1)) (.mkEmpty (capacity + 1))

@[inline]
def splitRoot (m : α) (v : β) (l r : BTreeNode α β) : BTreeNode α β :=
  .internal (Array.mkEmpty (capacity + 1) |>.push m) (Array.mkEmpty (capacity + 1) |>.push v)
    (Array.mkEmpty (2 * b + 1) |>.push l |>.push r)

inductive WF : BTreeNode α β → Prop where
  | leaf {keys values} : keys.size = values.size → WF (.leaf keys values)
  | internal {keys values} {children : Array (BTreeNode α β)} : values.size = keys.size →
      children.size = keys.size + 1 → (∀ (i : Nat) h, WF children[i]) →
      WF (.internal keys values children)

theorem WF.size_values {n : BTreeNode α β} (h : n.WF) : n.values.size = n.keys.size := by
  cases h <;> simp_all [keys, values]

theorem WF.size_children {keys values} {children : Array (BTreeNode α β)}
    (h : (BTreeNode.internal keys values children).WF) : children.size = keys.size + 1 := by
  cases h; assumption

theorem WF.child {keys values} {children : Array (BTreeNode α β)}
    (h : (BTreeNode.internal keys values children).WF) (i : Nat) {h'} : (children[i]'h').WF := by
  cases h; rename_i h _; apply h

theorem wf_empty : (empty α β : BTreeNode α β).WF :=
  .leaf (by simp)

@[inline] def get? (cmp : α → α → Ordering) (key : α) (n : BTreeNode α β) (hn : n.WF) : Option β :=
  go 0 (Nat.zero_le _)
termination_by (sizeOf n, n.keys.size + 2)
where
  go (i : Nat) (hi : i ≤ n.keys.size) : Option β :=
    if h : i = n.keys.size then
      recur i hi
    else
      match cmp key n.keys[i] with
      | Ordering.lt => recur i hi
      | Ordering.gt => go (i + 1) (by omega)
      | Ordering.eq =>
          have : i < n.values.size := by rw [hn.size_values]; omega
          some n.values[i]
  termination_by (sizeOf n, n.keys.size - i + 1)
  @[inline] recur (i : Nat) (_h : i ≤ n.keys.size) : Option β :=
    match n with
    | .leaf _ _ => none
    | .internal _ _ children =>
        have : i < children.size := by simp [hn.size_children, keys] at *; omega
        get? cmp key children[i] (hn.child _)
  termination_by (sizeOf n, 0)

@[inline]
def setValue : (n : BTreeNode α β) → (hn : n.WF) → (i : USize) → (hi : i.toNat < n.keys.size) → β → BTreeNode α β
  | BTreeNode.leaf keys values, hn, i, hi, v =>
      .leaf keys (values.uset i v (by cases hn; simp [BTreeNode.keys] at *; omega))
  | BTreeNode.internal keys values children, hn, i, hi, v =>
      .internal keys (values.uset i v (by cases hn; simp [BTreeNode.keys] at *; omega)) children

theorem WF.setValue {n : BTreeNode α β} (hn : n.WF) {i : USize} {hi : i.toNat < n.keys.size} {v : β} :
    (n.setValue hn i hi v).WF := by
  cases n with
  | leaf keys values =>
      simp only [BTreeNode.setValue]
      cases hn
      exact WF.leaf (by simpa)
  | internal keys values children =>
      simp only [BTreeNode.setValue]
      cases hn
      apply WF.internal <;> simpa

theorem WF.set {keys values} {children : Array (BTreeNode α β)} (hn : (BTreeNode.internal keys values children).WF)
    {i : Fin children.size} {t : BTreeNode α β} (ht : t.WF) :
    (BTreeNode.internal keys values (children.set i t)).WF := by
  cases hn with
  | internal h₁ h₂ h₃ =>
    refine WF.internal h₁ (by simpa) (fun j hj => ?_)
    rw [Array.getElem_set]
    split
    · exact ht
    · exact h₃ j _

theorem wf_splitRoot {m v l} {r : BTreeNode α β} (hl : l.WF) (hr : r.WF) :
    (splitRoot m v l r).WF := by
  refine .internal (by simp) (by simp) (fun i hle => ?_)
  match i, hle with
  | 0, _ => simpa [Array.get_push]
  | 1, _ => simpa [Array.get_push]

inductive InsertResult (α : Type u) (β : Type v) where
  | ok : (res : BTreeNode α β) → res.WF → InsertResult α β
  | split : α → β → (l : BTreeNode α β) → (r : BTreeNode α β) → l.WF → r.WF → InsertResult α β

@[inline]
def splitArray (as : Array α) (n : Nat) : Array α × Array α :=
  Array.iSplit as n (capacity + 2)

-- @[inline]
-- def splitArray (as : Array α) (n : Nat) : Array α × Array α :=
--   let rhs := copyOver as n (Array.mkEmpty (capacity + 2))
--   ((dbgTraceIfShared "asas" as).shrink n, rhs)
-- where
--   copyOver (src : Array α) (i : Nat) (dest : Array α) : Array α :=
--     if h : i ≥ src.size then
--       dest
--     else
--       copyOver src (i + 1) (dest.push src[i])
--     termination_by src.size - i

@[inline]
def splitLeafIfNecessary (keys : Array α) (values : Array β) (h : (BTreeNode.leaf keys values).WF) :
    InsertResult α β :=
  if keys.size ≤ capacity then
    .ok (.leaf keys values) h
  else
    -- have : keys.size = capacity + 1 := sorry -- trust me
    let (leftKeys, rightKeys) := splitArray (dbgTraceIfShared "zzz1" keys) b
    have : leftKeys.size = b := sorry
    have : rightKeys.size = b := sorry
    let (leftValues, rightValues) := splitArray (dbgTraceIfShared "yyy1" values) b
    have : leftValues.size = b := sorry
    have : rightValues.size = b := sorry
    let medianKey := leftKeys[b - 1]'(by simp [b] at *; omega)
    let medianValue := leftValues[b - 1]'(by simp [b] at *; omega)
    .split medianKey medianValue (.leaf (dbgTraceIfShared "uuu" leftKeys).pop leftValues.pop) (.leaf rightKeys rightValues) sorry sorry

@[inline]
def splitInternalIfNecessary (keys : Array α) (values : Array β) (children : Array (BTreeNode α β))
    (h : (BTreeNode.internal keys values children).WF) : InsertResult α β :=
  if keys.size ≤ capacity then
    .ok (.internal keys values children) h
  else
    -- have : keys.size = capacity + 1 := sorry -- trust me
    let (leftKeys, rightKeys) := splitArray (dbgTraceIfShared "zzz" keys) b
    have : leftKeys.size = b := sorry
    have : rightKeys.size = b := sorry
    let (leftValues, rightValues) := splitArray (dbgTraceIfShared "yyy" values) b
    have : leftValues.size = b := sorry
    have : rightValues.size = b := sorry
    let medianKey := leftKeys[b - 1]'(by simp [b] at *; omega)
    let medianValue := leftValues[b - 1]'(by simp [b] at *; omega)
    let (leftChildren, rightChildren) := splitArray (dbgTraceIfShared "xxx" children) b
    have : leftChildren.size = b := sorry
    have : rightChildren.size = b + 1 := sorry
    .split medianKey medianValue (.internal leftKeys.pop leftValues.pop leftChildren) (.internal rightKeys rightValues rightChildren) sorry sorry

instance : Inhabited { n' : BTreeNode α β // n'.WF } := sorry
instance : Inhabited (InsertResult α β) := sorry

-- set_option trace.compiler.ir.reset_reuse true in
partial def insert (cmp : α → α → Ordering) (key : α) (value : β) (n : BTreeNode α β) (hn : n.WF) :
    { n' : BTreeNode α β // n'.WF } :=
  match go n hn with
  | .ok newRoot hn => ⟨newRoot, hn⟩
  | .split m v l r hl hr => ⟨.splitRoot m v l r, wf_splitRoot hl hr⟩
where
  go (curNode : BTreeNode α β) (hcur : curNode.WF) : InsertResult α β :=
    doNode curNode hcur 0 (Nat.zero_le _)
  doNode (curNode : BTreeNode α β) (hcur : curNode.WF) (i : USize) (hi : i.toNat ≤ curNode.keys.size) : InsertResult α β :=
    if h : i.toNat = curNode.keys.size then
      descend curNode hcur i hi
    else
      match cmp key curNode.keys[i] with
      | Ordering.lt => descend curNode hcur i hi
      | Ordering.gt => doNode curNode hcur (i + 1) sorry
      | Ordering.eq => .ok (curNode.setValue hcur i (by omega) value) hcur.setValue
  descend (curNode : BTreeNode α β) (hcur : curNode.WF) (i : USize) (h : i.toNat ≤ curNode.keys.size) : InsertResult α β :=
    match curNode with
    | .leaf keys values =>
          let newKeys := (dbgTraceIfShared "cc" keys).fastInsertAt i key sorry
          let newValues := (dbgTraceIfShared "dd" values).fastInsertAt i value sorry
        splitLeafIfNecessary newKeys newValues (.leaf sorry)
    | .internal keys values children =>
        have : i.toNat < children.size := by simp [hcur.size_children, BTreeNode.keys] at *; omega
        let child := children[i]
        let children := children.uset i (empty _ _) this
        match go child (hcur.child _) with
        | .ok t ht => .ok (.internal keys values ((dbgTraceIfShared "cc" children).uset i t sorry)) sorry
        | .split k v l r hl hr =>
            let newKeys := (dbgTraceIfShared "aa" keys).fastInsertAt i k sorry
            let newValues := (dbgTraceIfShared "bb" values).fastInsertAt i v sorry
            let newChildren := (dbgTraceIfShared "dd" children).uset i r sorry
            let newChildren' := (dbgTraceIfShared "ee" newChildren).fastInsertAt i l sorry
            splitInternalIfNecessary newKeys newValues newChildren' (by sorry)
              -- cases hcur with
              -- | internal h₁ h₂ h₃ =>
              --   refine .internal ?_ ?_ ?_
              --   · simp [newKeys, newValues]; omega
              --   · simp [newKeys, newChildren', newChildren, dbgTraceIfShared]; omega
              --   · intro j hj
              --     simp only [newChildren, newChildren'] at *
              --     rw [Array.getElem_insertAt]
              --     split
              --     · next hji =>
              --       dsimp at hji
              --       rw [Array.getElem_set]
              --       simp [hji]
              --       split
              --       · exact hr
              --       · exact h₃ _ _
              --     · next hji =>
              --       split
              --       · exact hl
              --       · rw [Array.getElem_set]
              --         split
              --         · exact hr
              --         · exact h₃ _ _)

-- def s1 := (empty Nat Nat).insert (Ord.compare) 2 5 wf_empty
-- def s2 := s1.1.insert Ord.compare 3 7 s1.2

-- def s3 : BTreeNode Nat Nat := Id.run do
--   let mut ans : BTreeNode Nat Nat := empty Nat Nat
--   for i in [0:12] do
--     ans := ans.insert Ord.compare ((37 * i) % 200) i sorry
--   ans

-- #eval s3

-- #eval BTreeNode.get? Ord.compare 199 s3 sorry

end BTreeNode

end Lean
