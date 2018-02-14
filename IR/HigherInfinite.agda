module IR.HigherInfinite where

open import MLTT.MLTT

data U₁ : Set
T₁ : U₁ → Set

data U₁ where
  u : U₁
  i : U → U₁
  π : (a : U₁) -> (T₁ a -> U₁) -> U₁
-- also closed under everything else that U is closed under

T₁ u = U
T₁ (i a) = T a
T₁ (π a b) = Π (T₁ a) (λ x -> T₁ (b x))


data NextU (A : Set) (B : A → Set) : Set
NextT : (A : Set) → (B : A → Set) → NextU A B → Set

data NextU (A : Set) (B : A → Set) where
  u : NextU A B
  i : A → NextU A B
  π : (a : NextU A B) -> (NextT A B a -> NextU A B) -> NextU A B
-- also closed under everything else that U is closed under

NextT A B u = A
NextT A B (i a) = B a
NextT A B (π a b) =  Π (NextT A B a) (λ x -> NextT A B (b x))


data SuperU : Set
SuperT : SuperU → Set

data SuperU where
  u : SuperU
  nextU : (a : SuperU) → (b : SuperT a → SuperU) → SuperU
  nextT : (a : SuperU) → (b : SuperT a → SuperU) → SuperT (nextU a b) → SuperU
  π : (a : SuperU) -> (SuperT a -> SuperU) -> SuperU
-- also closed under everything else that U is closed under

SuperT u = U
SuperT (nextU a b) = NextU (SuperT a) (λ x → SuperT (b x))
SuperT (nextT a b x) = NextT (SuperT a) (λ x → SuperT (b x)) x
SuperT (π a b) = Π (SuperT a) (λ x -> SuperT (b x))


-- Mahlo universe is obtained by closing up under an arbitary "next universe operator f,g"
-- we postulate them, but they should really be parameters of
-- the inductive-recursive definition
-- Note that f, g generalize NextU, NextT

postulate
  f : (A : Set) → (B : A → Set) → Set
  g : (A : Set) → (B : A → Set) → f A B → Set
   
data MahloU : Set
MahloT : MahloU → Set

data MahloU where
  f-code : (a : MahloU) → (MahloT a → MahloU)
    → MahloU
  g-code : (a : MahloU) → (b : MahloT a → MahloU)
    → f (MahloT a) (λ x → MahloT (b x)) → MahloU

-- we should also close up under u, π, etc

MahloT (f-code a b)   = f (MahloT a) (λ x → MahloT (b x))
MahloT (g-code a b c) = g (MahloT a) (λ x → MahloT (b x)) c


