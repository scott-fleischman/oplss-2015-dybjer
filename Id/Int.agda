-- Three representations of integers

module Id.Int where

open import IType.Nat
open import IType.Bool

-- integers as a set: a unique representation of each integer

data Z : Set where
  O : Z
  +1_ : Nat → Z
  -1_ : Nat → Z

-- integers as pairs of natural numbers - a setoid

data Z' : Set where
  _#_ : Nat → Nat → Z'

normalize : Z' → Z'
normalize (zero # n) = zero # n
normalize (succ m # zero) = succ m # zero
normalize (succ m # succ n) = normalize (m # n)

idZ' : Z' → Z' → Bool
idZ' (m # n) (m' # n') = eqNat m m' && eqNat n n'

eqZ' : Z' → Z' → Bool
eqZ' i j = idZ' (normalize i) (normalize j)

-- integers with + 0 = - 0, another setoid

data Z'' : Set where
  + : Nat → Z''
  - : Nat → Z''

eqZ'' : Z'' → Z'' → Bool
eqZ'' (+ m) (+ n) = eqNat m n
eqZ'' (+ m) (- n) = isZero m && isZero n
eqZ'' (- m) (+ n) = isZero m && isZero n
eqZ'' (- m) (- n) = eqNat m n

-- Some functions on Z:

inj+ : Nat → Z
inj+ zero = O
inj+ (succ n) = +1 n

inj- : Nat → Z
inj- zero = O
inj- (succ n) = -1 n

succZ : Z → Z
succZ O = +1 zero
succZ (+1 n) = +1 succ n
succZ (-1 n) = -1 pred n

  
