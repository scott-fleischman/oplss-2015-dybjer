module Id.Real where

open import IType.Nat hiding (_-_)
open import MLTT.MLTT hiding (_+_)

postulate
  Q : Set
  zeroQ : Q
  _>_ : Q → Q → Set
  minusQ : Q → Q → Q
  absQ : Q → Q

-- Real numbers as Cauchy sequences of rationals

Cauchy : (Nat → Q) → Set
Cauchy x = (ε : Q) → ε > zeroQ
  → Σ Nat (λ m → (n : Nat) → ε > absQ (minusQ (x (m + n)) (x m)))

Real : Set
Real = Σ (Nat → Q) Cauchy

eqReal : Real → Real → Set
eqReal (x , p) (y , q) = (ε : Q) → ε > zeroQ
  → Σ Nat (λ m → (n : Nat) → ε > absQ (minusQ (x (m + n)) (y (m + n)))
