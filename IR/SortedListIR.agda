module IR.SortedListIR where

open import IType.Nat
open import IType.Bool
open import MLTT.PredicateLogic

data SortedList : Set
hd : SortedList → Nat

data SortedList where
  [_]  : Nat → SortedList
  cons : (n : Nat)
    → (ns : SortedList)
    → So (n < hd ns)
    → SortedList

hd [ n ] = n
hd (cons n ns p) = n

--
-- data MyList: Set where
--   nil : MyList
--  cons : (n : Nat) → (ns : MyList) → (n > sum ns) → MyList

-- sum nil = zero
-- sum (cons n ns _) = n + sum ns
