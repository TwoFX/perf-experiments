/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace MyLean
universe u v w w'

inductive RBColor where
  | red | black

inductive RBNode (α : Type) (β : α → Type) where
  | leaf                                                                                        : RBNode α β
  | node (c : RBColor) (lchild : RBNode α β) (key : α) (val : β key) (rchild : RBNode α β) : RBNode α β

open RBColor

namespace RBNode
variable {α : Type} {β : α → Type} {σ : Type w}

open Nat

def depth (f : Nat → Nat → Nat) : RBNode α β → Nat
  | leaf           => 0
  | node _ l _ _ r => succ (f (depth f l) (depth f r))

def singleton (k : α) (v : β k) : RBNode α β :=
  node red leaf k v leaf

-- the first half of Okasaki's `balance`, concerning red-red sequences in the left child
@[inline] def balance1 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | node red (node red a kx vx b) ky vy c, kz, vz, d
  | node red a kx vx (node red b ky vy c), kz, vz, d => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a,                                     kx, vx, b => node black a kx vx b

-- the second half, concerning red-red sequences in the right child
@[inline] def balance2 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | a, kx, vx, node red (node red b ky vy c) kz vz d
  | a, kx, vx, node red b ky vy (node red c kz vz d) => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a, kx, vx, b                                     => node black a kx vx b

@[inline]
def isRed : RBNode α β → Bool
  | node red .. => true
  | _           => false

@[inline]
def isBlack : RBNode α β → Bool
  | node black .. => true
  | _             => false

section Insert

variable {m : Type → Type} [Monad m]

-- variable (cmp : α → α → m Ordering)

@[specialize] def ins [Ord α] : RBNode α β → (k : α) → β k → RBNode α β
  | leaf,               kx, vx => node red leaf kx vx leaf
  | node red a ky vy b, kx, vx =>
    match compare kx ky with
    | Ordering.lt => node red (ins a kx vx) ky vy b
    | Ordering.gt => node red a ky vy (ins b kx vx)
    | Ordering.eq => node red a kx vx b
  | node black a ky vy b, kx, vx =>
    match compare kx ky with
    | Ordering.lt => balance1 (ins a kx vx) ky vy b
    | Ordering.gt => balance2 a ky vy (ins b kx vx)
    | Ordering.eq => node black a kx vx b

@[inline]
def setBlack : RBNode α β → RBNode α β
  | node red l k v r => node black l k v r
  | e              => e

@[specialize] def insert [Ord α] (t : RBNode α β) (k : α) (v : β k) : RBNode α β :=
  if isRed t then setBlack (ins t k v)
  else ins t k v

@[specialize] def find [Ord α] {β : Type} : RBNode α (fun _ => β) → α → Option β
  | leaf,             _ => none
  | node _ a ky vy b, x =>
    match compare x ky with
    | Ordering.lt => find a x
    | Ordering.gt => find b x
    | Ordering.eq => some vy

end Insert

end RBNode
