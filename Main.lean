set_option autoImplicit false

inductive TreeNode where
  | inner (size : Nat) (l r : TreeNode)
  | leaf

namespace TreeNode

@[inline]
def balanceR (l r : TreeNode) : TreeNode :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 .leaf .leaf
    | r@(inner _ .leaf .leaf) => .inner 2 .leaf r
    | inner _ .leaf rr@(.inner _ _ _) => .inner 3 (.inner 1 .leaf .leaf) rr
    | inner _ (.inner _ _ _) .leaf => .inner 3 (.inner 1 .leaf .leaf) (.inner 1 .leaf .leaf)
    | _ => .leaf
  | l@(inner ls _ _) => match r with
    | leaf => .inner (1 + ls) l .leaf
    | r@(inner rs rl rr) =>
        if rs > 2 * ls then match rl, rr with
          | inner rls _ _, .inner _ _ _ =>
              .inner (1 + ls + rs) (.inner (1 + ls + rls) l rl) rr
          | _, _ => .leaf
        else .inner (1 + ls + rs) l r

set_option trace.compiler.ir.result true in
def insert : TreeNode → TreeNode
| leaf => .inner 1 .leaf .leaf
| inner _ l r => balanceR l (insert r)

end TreeNode

def sz : Nat := 1000000

@[noinline] def growInsertB (numbers : Array Nat) : IO TreeNode := do
  let mut m : TreeNode := .leaf
  for _ in numbers do
    m := m.insert
  return m

def main : IO Unit := do
  let numbers := Array.range sz
  for _ in [:5] do
    let _ ← timeit "" $ growInsertB numbers
  println! "-------------------"
