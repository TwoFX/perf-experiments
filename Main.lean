set_option autoImplicit false

universe u v

variable {α : Type}

inductive TreeNode (α : Type) where
  | inner (size : Nat) (k : α) (l r : TreeNode α)
  | leaf

namespace TreeNode

@[inline]
def delta : Nat := 3
@[inline]
def ratio : Nat := 2

@[inline]
def size : TreeNode α → Nat
  | inner s _ _ _ => s
  | leaf => 0

instance : Inhabited (TreeNode α) where
  default := .leaf

@[inline] def balanceR (k : α) (l r : TreeNode α) : TreeNode α :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k .leaf .leaf
    | r@(inner _ _ .leaf .leaf) => .inner 2 k .leaf r
    | inner _ rk .leaf rr@(.inner _ _ _ _) => .inner 3 rk (.inner 1 k .leaf .leaf) rr
    | inner _ rk (.inner _ rlk _ _) .leaf => .inner 3 rlk (.inner 1 k .leaf .leaf) (.inner 1 rk .leaf .leaf)
    | _ => panic! "Unexpected"
  | l@(inner ls _ _ _) => match r with
    | leaf => .inner (1 + ls) k l .leaf
    | r@(inner rs rk rl rr) =>
        if rs > delta * ls then match rl, rr with
          | inner rls rlk rll rlr, .inner rrs _ _ _ =>
              if rls < ratio * rrs then .inner (1 + ls + rs) rk (.inner (1 + ls + rls) k l rl) rr
              else .inner (1 + ls + rs) rlk (.inner (1 + ls + rll.size) k l rll) (.inner (1 + rrs + rlr.size) rk rlr rr)
          | _, _ => panic! "Unexpected case"
        else .inner (1 + ls + rs) k l r

def insert (k : α) : TreeNode α → TreeNode α
| leaf => .inner 1 k .leaf .leaf
| inner _ ky l r => balanceR ky l (insert k r)

end TreeNode

open Lean

def sz : Nat := 300000

@[noinline] def growInsertB (numbers : Array Nat) : IO (TreeNode Nat) := do
  let mut m : TreeNode Nat := .leaf
  let mut i := 0
  for s in numbers do
    m := m.insert s
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
