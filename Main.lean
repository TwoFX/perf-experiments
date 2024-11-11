set_option autoImplicit false

inductive TreeNode where
  | inner (size : Nat) (l r : TreeNode)
  | leaf

namespace TreeNode

@[inline]
def size : TreeNode → Nat
| inner sz _ _ => sz
| leaf => 0

@[inline]
def balanceR (l r : TreeNode) : TreeNode :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 .leaf .leaf
    | r@(inner _ .leaf .leaf) => .inner 2 .leaf r
    | inner _ .leaf rr@(.inner _ _ _) => .inner 3 (.inner 1 .leaf .leaf) rr
    | inner _ (.inner _ _ _) .leaf => .inner 3 (.inner 1 .leaf .leaf) (.inner 1 .leaf .leaf)
    | _ => False.elim sorry
  | l@(inner ls _ _) => match r with
    | leaf => .inner (1 + ls) l .leaf
    | r@(inner rs rl rr) =>
        if rs > 2 * ls then
          match rl, rr with
          | inner rls rll rlr, .inner rrs _ _ =>
              if rls < 2 * rrs then
                .inner (1 + ls + rs) (.inner (1 + ls + rls) l rl) rr
              else
                .inner (1 + ls + rs) (.inner (1 + ls + rll.size) l rll)
                  (.inner (1 + rrs + rlr.size) rlr rr)

        -- match rl, rr with
        --   | inner rls _ _, .inner _ _ _ =>
        --       .inner (1 + ls + rs) (.inner (1 + ls + rls) l rl) rr
          | _, _ => False.elim sorry
        else .inner (1 + ls + rs) l r

set_option trace.compiler.ir.result true in
def insert : TreeNode → TreeNode
| leaf => .inner 1 .leaf .leaf
| inner _ l r => balanceR l (insert r)

end TreeNode

def sz : Nat := 1000000

@[noinline] def growInsertB : IO TreeNode := do
  let mut m : TreeNode := .leaf
  for _ in [:sz] do
    m := m.insert
  return m

def main : IO Unit := do
  for _ in [:5] do
    let _ ← timeit "" growInsertB
  println! "-------------------"
