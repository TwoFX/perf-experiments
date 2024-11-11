set_option autoImplicit false

namespace LE

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
    | inner ls lk lv ll@(.inner lls _ _ _ _) lr@(.inner lrs lrk lrv lrl lrr) =>
        if lrs < ratio * lls then .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf)
        else .inner (1 + ls) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl) (.inner (1 + lrr.size) k v lrr .leaf)
  | r@(inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | l@(inner ls lk lv ll lr) =>
        if ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl) (.inner (1 + rs + lrr.size) k v lrr r)
          | _, _ => False.elim sorry
        else .inner (1 + ls + rs) k v l r

@[inline] def balanceR (k : α) (v : β) (l r : TreeNode α β) : TreeNode α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf) (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
        else .inner (1 + rs) rlk rlv (.inner (1 + rll.size) k v .leaf rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | l@(inner ls _ _ _ _) => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | r@(inner rs rk rv rl rr) =>
        if rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | _, _ => False.elim sorry
        else .inner (1 + ls + rs) k v l r

variable {m : Type → Type} [Monad m]

@[inline, always_inline, specialize]
def chk (cmp : α → α → m Bool) (a b : α) : m Ordering := do
  match ← cmp a b with
  | false => return .gt
  | true => match ← cmp b a with
    | false => return .lt
    | true => return .eq

@[specialize] def insert (cmp : α → α → m Bool) (k : α) (v : β) : TreeNode α β → m (TreeNode α β)
| leaf => pure <| .inner 1 k v .leaf .leaf
| inner sz ky y l r => do match (← chk cmp k ky) with
    | .lt => return balanceL ky y (← insert cmp k v l) r
    | .eq => return .inner sz ky v l r
    | .gt => return balanceR ky y l (← insert cmp k v r)

@[specialize] def find (cmp : α → α → m Bool) (k : α) : TreeNode α β → m (Option β)
| leaf => pure none
| inner _ ky y l r => do
    match ← chk cmp k ky with
    | .lt => find cmp k l
    | .gt => find cmp k r
    | .eq => return some y

@[specialize] def insertionPoint (cmp : α → α → m Bool) (k : α) (t : TreeNode α β) : m Nat :=
  go 0 t
where
  @[specialize] go (sofar : Nat) : TreeNode α β → m Nat
  | leaf => pure sofar
  | inner _ ky _ l r => do
    match ← chk cmp k ky with
    | .lt => go sofar l
    | .eq => return sofar + size l
    | .gt => go (sofar + 1 + size l) r

def inversions (l : List Nat) : Nat := Id.run do
  let mut m : TreeNode Nat Unit := .leaf
  let mut ans := 0
  for x in l do
    let insPt : Nat := insertionPoint (m := Id) (fun x y => decide (x ≤ y)) x m
    ans := ans + (m.size - insPt)
    m := m.insert (m := Id) (fun x y => decide (x ≤ y)) x ()
  return ans

-- #eval! inversions [6,5,4,3,2,7,1]

def depth : TreeNode α β → Nat
| leaf => 0
| inner _ _ _ l r => 1 + max l.depth r.depth

end TreeNode

end LE
