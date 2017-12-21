module LambdaStructure where

open import Nat

mutual
  data Sub : Nat → Nat → Set where
    _∘_ : {m n p : Nat} → Sub n p → Sub m n → Sub m p
    id : {m : Nat} → Sub m m
    <> : {m : Nat} → Sub m zero
    <_,_> : {m n : Nat} → Sub m n → Raw n → Sub m (succ n)
  
  data Raw : Nat → Set where
    _[_] : {m n : Nat} → Raw n → Sub m n → Raw m
    Zero : {m : Nat} → Raw m
    Succ : {m : Nat} → Raw m → Raw m

-- a category with families with objects in Nat, arrows in Sub m n, only one type and terms in Raw m

data Val : Set where
  ZeroV : Val
  SuccV : Raw zero → Val
  NV    : Val



data _=>_ : Raw zero → Val → Set where
  subSub  : {m n p : Nat} → {a : Raw p} → {as : Sub n p} → {bs : Sub zero n}
          → {v : Val}
          → (a [ as ∘ bs ]) => v
          → ((a [ as ]) [ bs ])  => v
  succSub : {m : Nat} → {a : Raw m} → {as : Sub zero m}
          → (Succ a) [ as ] => SuccV (a [ as ])
  zeroSub : {m : Nat} → {as : Sub zero m} → Zero [ as ] => ZeroV
  zeroV : Zero => ZeroV
  succV : {a : Raw zero} → Succ a => SuccV a

data N : Raw zero → Set where
  zeroN : {a : Raw zero} → (a => ZeroV) → N a
  succN : {a b : Raw zero} → (a => SuccV b) → N b → N a

data _::_ : Raw zero → Raw zero → Set where
  zeroN : {a A : Raw zero} → (a => ZeroV) → (A => NV) → a :: A
  succN : {a b A : Raw zero} → (a => SuccV b) → (A => NV) → b :: A → a :: A

-- _⊢_::_ : {n : Nat} → Ctx n → Raw n → Raw n → Set
-- Γ ⊢ a :: A = γ :: Γ → a [ γ ] :: A [ γ ]




