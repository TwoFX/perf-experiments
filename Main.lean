set_option autoImplicit false

inductive TreeNode where
  | inner (size : Nat) (l r : TreeNode)
  | leaf

namespace TreeNode

@[inline]
def delta : Nat := 3
@[inline]
def ratio : Nat := 2

@[inline]
def size : TreeNode → Nat
  | inner s _ _ => s
  | leaf => 0

instance : Inhabited TreeNode where
  default := .leaf

@[inline] def balanceR (l r : TreeNode) : TreeNode :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 .leaf .leaf
    | r@(inner _ .leaf .leaf) => .inner 2 .leaf r
    | inner _ .leaf rr@(.inner _ _ _) => .inner 3 (.inner 1 .leaf .leaf) rr
    | inner _ (.inner _ _ _) .leaf => .inner 3 (.inner 1 .leaf .leaf) (.inner 1 .leaf .leaf)
    | _ => panic! "Unexpected"
  | l@(inner ls _ _) => match r with
    | leaf => .inner (1 + ls) l .leaf
    | r@(inner rs rl rr) =>
        if rs > delta * ls then match rl, rr with
          | inner rls rll rlr, .inner rrs _ _ =>
              if rls < ratio * rrs then .inner (1 + ls + rs) (.inner (1 + ls + rls) l rl) rr
              else .inner (1 + ls + rs) (.inner (1 + ls + rll.size) l rll) (.inner (1 + rrs + rlr.size) rlr rr)
          | _, _ => panic! "Unexpected case"
        else .inner (1 + ls + rs) l r

def insert : TreeNode → TreeNode
| leaf => .inner 1 .leaf .leaf
| inner _ l r => balanceR l (insert r)

end TreeNode

open Lean

def sz : Nat := 300000

@[noinline] def growInsertB (numbers : Array Nat) : IO TreeNode := do
  let mut m : TreeNode := .leaf
  let mut i := 0
  for _ in numbers do
    m := m.insert
    i := i + 1
  return m

-- def p : Nat := 10^9 + 7

-- def powModNaive (a b p : Nat) : IO Nat := do
--   let mut ans : Nat := 1
--   let mut q := 0
--   for _ in [:b] do
--     ans := (ans * a) % p
--     if ans > 100 then
--       q := q + 1
--   return q

def main : IO Unit := do
  let numbers := Array.range sz
  for _ in [:5] do
    -- let _ ← timeit "" $ powModNaive 2 10000000 p
    let _ ← timeit "" $ growInsertB numbers
  println! "-------------------"
