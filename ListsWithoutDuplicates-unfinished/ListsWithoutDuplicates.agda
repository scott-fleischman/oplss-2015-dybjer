module FiniteSubsets.ListsWithoutDuplicates where

open import IType.Bool
open import IType.Nat
open import IType.List
open import MLTT.PropositionalLogic
open import FiniteSubsets.Interface
open import FiniteSubsets.ListsWithDuplicates

length : List Nat → Nat
length [] = 0
length (_ :: ns) = succ (length ns)

[_] : {A : Set} → A → List A
[ a ] = a :: []

insertFresh : Nat → List Nat → List Nat
insertFresh a []         = [ a ]
insertFresh a (a' :: as) = if eqNat a a' then a :: as else (a' :: insertFresh a as)

ax-member-insertFresh : (n : Nat) → (ns : List Nat)
  → So (member n (insertFresh n ns))
ax-member-insertFresh n [] = {!!}
ax-member-insertFresh n (n' :: ns) = if eqNat n n' then ax-member-cons n ns else ax-member-insertFresh n {!!}
{- 
ax-member-insertFresh n (n' :: ns) with eqNat n n'
ax-member-insertFresh n (n' :: ns) | true  = ax-member-cons n ns
ax-member-insertFresh n (n' :: ns) | false = ax-member-insertFresh n {!!}
--}

-- So (member m (insertFresh m ns))

step : (n n' : Nat) → (ns : List Nat) → So (eqNat n n') 
  → So (member n (insertFresh n ns)) → So (member n (if false then n :: ns else (n' :: insertFresh n ns)))
step n n' ns p hyp = ||-intro {!!} {!!} p

