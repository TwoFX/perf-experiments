/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace MyLean
universe u v w w'

inductive RBNode (α : Type) (β : α → Type) where
  | leaf                                                                                        : RBNode α β
  | red   (lchild : RBNode α β) (key : α) (val : β key) (rchild : RBNode α β) : RBNode α β
  | black (lchild : RBNode α β) (key : α) (val : β key) (rchild : RBNode α β) : RBNode α β

namespace RBNode
variable {α : Type} {β : α → Type} {σ : Type w}

open Nat

def depth (f : Nat → Nat → Nat) : RBNode α β → Nat
  | leaf           => 0
  | red l _ _ r => succ (f (depth f l) (depth f r))
  | black l _ _ r => succ (f (depth f l) (depth f r))

def singleton (k : α) (v : β k) : RBNode α β :=
  red leaf k v leaf

-- the first half of Okasaki's `balance`, concerning red-red sequences in the left child
@[inline] def balance1 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | red (red a kx vx b) ky vy c, kz, vz, d
  | red a kx vx (red b ky vy c), kz, vz, d => red (black a kx vx b) ky vy (black c kz vz d)
  | a,                                     kx, vx, b => black a kx vx b

-- the second half, concerning red-red sequences in the right child
@[inline] def balance2 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | a, kx, vx, red (red b ky vy c) kz vz d
  | a, kx, vx, red b ky vy (red c kz vz d) => red (black a kx vx b) ky vy (black c kz vz d)
  | a, kx, vx, b                                     => black a kx vx b

@[inline]
def isRed : RBNode α β → Bool
  | red .. => true
  | _           => false

@[inline]
def isBlack : RBNode α β → Bool
  | black .. => true
  | _             => false

section Insert

variable {m : Type → Type} [Monad m]

variable (cmp : α → α → m Ordering)

@[specialize] def ins : RBNode α β → (k : α) → β k → m (RBNode α β)
  | leaf,               kx, vx => pure <| red leaf kx vx leaf
  | red a ky vy b, kx, vx => do
    match ← cmp kx ky with
    | Ordering.lt => return red (← ins a kx vx) ky vy b
    | Ordering.gt => return red a ky vy (← ins b kx vx)
    | Ordering.eq => return red a kx vx b
  | black a ky vy b, kx, vx => do
    match ← cmp kx ky with
    | Ordering.lt => return balance1 (← ins a kx vx) ky vy b
    | Ordering.gt => return balance2 a ky vy (← ins b kx vx)
    | Ordering.eq => return black a kx vx b

@[inline]
def setBlack : RBNode α β → RBNode α β
  | red l k v r => black l k v r
  | e              => e

@[specialize] def insert (t : RBNode α β) (k : α) (v : β k) : m (RBNode α β) :=
  if isRed t then do return setBlack (← ins cmp t k v)
  else ins cmp t k v

end Insert

end RBNode
