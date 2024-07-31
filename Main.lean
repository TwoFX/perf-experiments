import «BTree»
import BTree.BoundedSize
import BTree.OtherRB

open Lean

def lowercase : List Char :=
  [ 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
    'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']


partial def fisherYates (a : Array α) : Array α := Id.run do
  let mut res := a
  let mut rng := mkStdGen
  for i in [0:a.size] do
    let (select, newRng) := randNat rng i (a.size - 1)
    rng := newRng
    res := res.swap ⟨i, sorry⟩ ⟨select, sorry⟩
  res

-- partial def mkStrings (len num : Nat) : Array String := Id.run do
--   if len = 0 then
--     return #[""]
--   let inner := mkStrings (len - 1) ((num + 25) / 26)
--   let mut hv : Nat := 0
--   let mut ans : Array String := #[]
--   for i in inner do
--     for c in lowercase do
--       ans := ans.push (i.push c)
--       hv := hv + 1
--       if hv = num then
--         break
--     if hv = num then
--       break
--   ans
-- abbrev α := String

def mkStrings (_len num : Nat) : Array Nat := Id.run do
  let mut ans := #[]
  for i in [0:num] do
    ans := ans.push i
  ans
abbrev α := Nat

abbrev m : Type → Type := StateM Nat

def cmpM : α → α → m Ordering := fun x y => do
  modify (· + 1)
  return Ord.compare x y
def cmp : α → α → Ordering := fun x y => Ord.compare x y
-- def cmp : α → α → Ordering := fun x y => .lt

@[noinline] def mkMyStrings (num len : Nat) : IO (Array α) := do
  return /-fisherYates-/ (mkStrings num len)


def sz : Nat := 300000

-- @[noinline] def growInsert' (strings : Array α) : BTreeNode α Nat := Id.run do
--   let mut m : BTreeNode α Nat := BTreeNode.empty _ _
--   let mut i := 0
--   for s in strings do
--     m := m.insert cmp s i sorry
--     i := i + 1
--   return m

-- @[noinline] def growInsert'' (a : Array α) : IO (BTreeNode α Nat) := do
--   return growInsert' a

-- @[noinline] def get' (string : α) (m : BTreeNode α Nat) : IO (Option Nat) := do
--   return m.get? cmp string sorry

-- @[noinline] def get (strings : Array α) (m : BTreeNode α Nat) : IO Unit := do
--   for s in strings do
--     discard <| get' s m

-- @[noinline] def growInsertL (strings : Array α) : (Lean.RBMap α Nat cmp) := Id.run do
--   let mut m : Lean.RBMap α Nat _ := Lean.mkRBMap _ _ _
--   let mut i := 0
--   for s in strings do
--     m := m.insert s i
--     i := i + 1
--   return m

-- @[noinline] def get'L (string : α) (m : Lean.RBMap α Nat cmp) : IO (Option Nat) := do
--   return m.find? string

-- @[noinline] def getL (strings : Array α) (m : Lean.RBMap α Nat cmp) : IO Unit := do
--   for s in strings do
--     discard <| get'L s m

-- @[noinline] def growInsertL' (strings : Array α) : IO (Lean.RBMap α Nat cmp) := do
--   let m := growInsertL strings
--   return m

@[noinline] def growInsertO (strings : Array α) : m (MyLean.RBNode α (fun _ => Nat)) := do
  let mut m : MyLean.RBNode α (fun _ => Nat) := .leaf
  let mut i := 0
  for s in strings do
    m ← m.insert cmpM s i
    i := i + 1
  return m

@[noinline] def growInsertO' (strings : Array α) : IO (MyLean.RBNode α (fun _ => Nat)) := do
  let m := StateT.run (growInsertO strings) 0
  println! "Comparisons: {m.2}"
  return m.1

@[noinline] def growInsertB (strings : Array α) : m (TreeNode α Nat) := do
  let mut m : TreeNode α Nat := .leaf
  let mut i := 0
  for s in strings do
    m := m.insert cmpM s i
    i := i + 1
  return m

@[noinline] def growInsertB' (a : Array α) : IO (TreeNode α Nat) := do
  let m := growInsertB a
  return m

@[noinline] def growInsertH (strings : Array α) : (Std.HashMap α Nat) := Id.run do
  let mut m : Std.HashMap α Nat := ∅
  let mut i := 0
  for s in strings do
    m := m.insert s i
    i := i + 1
  return m

@[noinline] def growInsertH' (a : Array α) : IO (Std.HashMap α Nat) := do
  return growInsertH a

def main (_ : List String) : IO UInt32 := do
  let strings ← timeit "mkMyStrings" $ mkMyStrings 8 sz
  for _ in [:20] do
    let _ ← timeit "Stupid BTree map" $ growInsert'' strings
  for _ in [:20] do
    let _ ← timeit "Stupid size-bounded map" $ growInsertB' strings
    -- let _ ← timeit "Stupid BTree map get" $ get strings m
  for _ in [:20] do
    let _ ← timeit "Lean RBTree" $ growInsertL' strings
  for _ in [:20] do
    let _ ← timeit "MyLean RBTree" $ growInsertO' strings
    -- let _ ← timeit "Lean RBTree get" $ getL strings m
  for _ in [:20] do
    let _ ← timeit "Std.HashMap" $ growInsertH' strings
  return 0
