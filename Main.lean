set_option autoImplicit false

variable {α : Type}

inductive TreeNode (α : Type) where
  | inner (size : Nat) (k : α) (l r : TreeNode α)
  | leaf

namespace TreeNode

@[inline]
def size : TreeNode α → Nat
  | inner s _ _ _ => s
  | leaf => 0

@[inline] def balanceR (k : α) (l r : TreeNode α) : TreeNode α :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k .leaf .leaf
    | r@(inner _ _ .leaf .leaf) => .inner 2 k .leaf r
    | inner _ rk .leaf rr@(.inner _ _ _ _) => .inner 3 rk (.inner 1 k .leaf .leaf) rr
    | inner _ rk (.inner _ rlk _ _) .leaf => .inner 3 rlk (.inner 1 k .leaf .leaf) (.inner 1 rk .leaf .leaf)
    | _ => False.elim sorry
  | l@(inner ls _ _ _) => match r with
    | leaf => .inner (1 + ls) k l .leaf
    | r@(inner rs rk rl rr) =>
        if rs > 3 * ls then match rl, rr with
          | inner rls rlk rll rlr, .inner rrs _ _ _ =>
              if rls < 2 * rrs then .inner (1 + ls + rs) rk (.inner (1 + ls + rls) k l rl) rr
              else .inner (1 + ls + rs) rlk (.inner (1 + ls + rll.size) k l rll) (.inner (1 + rrs + rlr.size) rk rlr rr)
          | _, _ => False.elim sorry
        else .inner (1 + ls + rs) k l r

@[specialize] def insert (cmp : α → α → Ordering) (k : α) : TreeNode α → TreeNode α
| leaf => .inner 1 k .leaf .leaf
| inner sz ky l r => match cmp k ky with
    | .gt => balanceR ky l (insert cmp k r)
    | _ => .inner sz ky l r

end TreeNode

open Lean

def sz : Nat := 300000

@[noinline] def growInsertB : IO (TreeNode Nat) := do
  let mut m : TreeNode Nat := .leaf
  for d in [:sz] do
    m := m.insert Ord.compare d
  return m

def main : IO Unit := do
  for _ in [:5] do
    let _ ← timeit "" $ growInsertB
  println! "-------------------"
