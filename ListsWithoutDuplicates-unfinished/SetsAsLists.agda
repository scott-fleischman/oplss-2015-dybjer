module Record.SetsAsLists where

-- sets as lists without repetitions

open import IType.List
open import IType.Bool
open import MLTT.PropositionalLogic

member : {A : Set} → (A → A → Bool) → A → List A → Bool
member eq a []         = false
member eq a (a' :: as) = (eq a a') || (member eq a as)

open import IType.Nat

length : {A : Set} → List A → Nat
length [] = zero
length (a :: as) = succ (length as)

[_] : {A : Set} → A → List A
[ a ] = a :: []

insertFresh : {A : Set} → (A → A → Bool) → A → List A → List A
insertFresh eq a []         = [ a ]
insertFresh eq a (a' :: as) = if eq a a' then a :: as else (a' :: insertFresh eq a as)

axproof : {A : Set}
  → (eq : A → A → Bool)
  → (refl : (a : A) → So (eq a a))
  → (a : A)
  → (as : List A)
  → So (member eq a (insertFresh eq a as))
axproof eq refl a [] = refl a
axproof eq refl a (a' :: as) with eq a a' 
axproof eq refl a (a' :: as) | true  = {!!}
axproof eq refl a (a' :: as) | false = {!!}

so-or : (a b : Bool) → So (a || b) → (So a ∨ So b)
so-or a true  p = ∨-intro₁ p
so-or a false p = ∨-intro₀ p

or-so : (a b : Bool) → (So a ∨ So b) → So (a || b)
or-so a     true  p = ⊤-intro
or-so true  false p = ⊤-intro
or-so false false (∨-intro₀ ())
or-so false false (∨-intro₁ ())
-- or-so a true  p = ⊤-intro
-- or-so a false (∨-intro₀ p) = p
-- or-so true false (∨-intro₁ ())
-- or-so false false (∨-intro₁ q) = q
