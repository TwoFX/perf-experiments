set_option autoImplicit false

variable {α : Type}

inductive TreeNode (α : Type) where
  | inner (size : Nat) (k : α) (l r : TreeNode α)
  | leaf

namespace TreeNode

@[specialize] def insert (cmp : α → α → Ordering) (k : α) : TreeNode α → TreeNode α
| leaf => .inner 1 k .leaf .leaf
| inner sz ky l₀ r₀ =>
    match cmp k ky with
    | .gt =>
        let r := insert cmp k r₀
        match l₀ with
        | leaf => match r with
          | leaf => .inner 1 k .leaf .leaf
          | r@(inner _ _ .leaf .leaf) => .inner 2 k .leaf r
          | inner _ rk _ rr => .inner 3 rk (.inner 1 k .leaf .leaf) rr
        | l@(inner ls _ _ _) => match r with
          | leaf => .inner (1 + ls) k l .leaf
          | r@(inner rs rk rl rr) =>
              if rs > 3 * ls then
                    .inner (1 + ls + rs) rk (.inner (1 + ls) k l rl) rr
              else .inner (1 + ls + rs) k l r
    | _ =>
      -- False.elim sorry
        .inner sz ky l₀ r₀

end TreeNode

@[noinline] def growInsertB : IO (TreeNode Nat) := do
  let mut m : TreeNode Nat := .leaf
  for d in [:10000000] do
    m := m.insert Ord.compare d
  return m

/- @[specialize] def insertL (cmp : α → α → Ordering) (k : α) : List α → List α
| [] => [k]
| x::xs => match cmp k x with
    | .gt => x :: insertL cmp k xs
    | _ => k :: x :: xs

@[noinline] def growInsertL : IO (List Nat) := do
  let mut m : List Nat := []
  for d in [:6000] do
    m := insertL Ord.compare d m
  return m

open Lean

def mkCascade (name : TSyntax `Lean.Parser.Command.declId) (depth : Nat) : MacroM (TSyntax `command) := do
  let body ← go 2 depth 0
  `(@[inline] def $name (n : Nat) := $body)
where
  go (cur max ans : Nat) : MacroM (TSyntax `term) := do
    if cur > max then
      return Syntax.mkNatLit ans
    else
      let lhs ← go (cur + 1) max (ans + 1)
      let rhs ← go (cur + 1) max ans
      let curLit := Syntax.mkNatLit cur
      `(if n % $curLit == 0 then $lhs else $rhs)
  termination_by max + 1 - cur

macro "cascade" n:declId : command => mkCascade n 12

cascade casc

def stupidL : IO Nat := do
  let mut ans : Nat := 0
  for d in [:10000000] do
    if casc d == 2 then
      ans := ans + 1
  return ans-/

def main : IO Unit := do
  for _ in [:5] do
    let _ ← timeit "" $ growInsertB
  println! "-------------------"
