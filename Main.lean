set_option autoImplicit false

universe u v

variable {α : Type} {β : Type}

inductive TreeNode (α : Type) (β : Type) where
  | inner (size : Nat) (k : α) (v : β) (l r : TreeNode α β)
  | leaf

namespace TreeNode

@[inline]
def delta : Nat := 3
@[inline]
def ratio : Nat := 2

@[inline]
def size : TreeNode α β → Nat
  | inner s _ _ _ _ => s
  | leaf => 0

instance : Inhabited (TreeNode α β) where
  default := .leaf

@[inline] def balanceL (k : α) (v : β) (l r : TreeNode α β) : TreeNode α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | l@(inner _ _ _ .leaf .leaf) => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | _ => panic! "Unexpected"
  | r@(inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | l@(inner ls lk lv ll lr) =>
        if ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl) (.inner (1 + rs + lrr.size) k v lrr r)
          | _, _ => panic! "Unexpected case"
        else .inner (1 + ls + rs) k v l r

@[inline] def balanceR (k : α) (v : β) (l r : TreeNode α β) : TreeNode α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf) (.inner 1 rk rv .leaf .leaf)
    | _ => panic! "Unexpected"
  | l@(inner ls _ _ _ _) => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | r@(inner rs rk rv rl rr) =>
        if rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | _, _ => panic! "Unexpected case"
        else .inner (1 + ls + rs) k v l r

@[specialize] def insert (cmp : α → α → Ordering) (k : α) (v : β) : TreeNode α β → TreeNode α β
| leaf => .inner 1 k v .leaf .leaf
| inner sz ky y l r => match cmp k ky with
    | .lt => balanceL ky y (insert cmp k v l) r
    | .eq => .inner sz ky v l r
    | .gt => balanceR ky y l (insert cmp k v r)

end TreeNode

open Lean

def mkStrings (num : Nat) : Array Nat := Id.run do
  let mut ans := #[]
  for i in [0:num] do
    ans := ans.push i
  for i in [0:num/2] do
    ans := ans.push (2 * i)
  ans

@[noinline] def mkMyStrings (num : Nat) : IO (Array Nat) := do
  return  (mkStrings num)

def sz : Nat := 300000

@[noinline] def growInsertB (strings : Array Nat) : TreeNode Nat Nat := Id.run do
  let mut m : TreeNode Nat Nat := .leaf
  let mut i := 0
  for s in strings do
    m := m.insert Ord.compare s i
    i := i + 1
  return m

@[noinline] def growInsertB' (a : Array Nat) : IO (TreeNode Nat Nat) := do
  return growInsertB a

def main : IO Unit := do
  let strings ← mkMyStrings sz
  for _ in [:5] do
    let _ ← timeit "" $ growInsertB' strings
  println! "-------------------"
