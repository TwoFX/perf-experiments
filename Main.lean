import BTree.BoundedSize

open Lean

def mkStrings (num : Nat) : Array Nat := Id.run do
  let mut ans := #[]
  for i in [0:num] do
    ans := ans.push i
  for i in [0:num/2] do
    ans := ans.push (2 * i)
  ans

def cmp : Nat → Nat → Ordering := fun x y => Ord.compare x y

@[noinline] def mkMyStrings (num : Nat) : IO (Array Nat) := do
  return  (mkStrings num)

def sz : Nat := 300000

@[noinline] def growInsertB (strings : Array Nat) : TreeNode Nat Nat := Id.run do
  let mut m : TreeNode Nat Nat := .leaf
  let mut i := 0
  for s in strings do
    m := m.insert cmp s i
    i := i + 1
  return m

@[noinline] def growInsertB' (a : Array Nat) : IO (TreeNode Nat Nat) := do
  return growInsertB a

def main : IO Unit := do
  let strings ← mkMyStrings sz
  for _ in [:5] do
    let _ ← timeit "" $ growInsertB' strings
  println! "-------------------"
