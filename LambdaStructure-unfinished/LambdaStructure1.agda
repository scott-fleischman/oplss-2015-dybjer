module LambdaStructure1 where

-- do it for Gödel System T with lazy numbers

open import Nat
open import Fin

mutual

  data Ty : Set where
    Fun : Ty → Ty → Ty
    Na : Ty → Ty → Ty

  data Ctx : Nat → Set where
    [] : Ctx zero
    _::_ : {n : Nat} → Ctx n → Ty → Ctx (succ n)
    
  data Sub : Nat → Nat → Set where
--    _∘_ : {m n p : Nat} → Sub n p → Sub m n → Sub m p
--    p : {m : Nat} → Sub (succ m) m
    <> : {m : Nat} → Sub m zero
    <_,_> : {m n : Nat} → Sub m n → Raw n → Sub m (succ n)

  data Raw : Nat → Set where
--    q : {m : Nat} → Tm (succ m)
    Zero : {m : Nat} → Raw m
    Succ : {m : Nat} → Raw m → Raw m
    Rec : {m : Nat} → Raw m → Raw (succ (succ m)) → Raw m → Raw m
    App : {m : Nat} → Raw m → Raw m → Raw m
    Lam : {m : Nat} → Raw (succ m) → Raw m
    Var : {m : Nat} → Fin m → Raw m

id : {m : Nat} → Sub m m
id {zero} = <>
id {succ m} = < {!!} , Var {!!} >

_[_] : {m n : Nat} → Raw n → Sub m n → Raw m
b [ as ] = {!!}

-- a category with families with objects in Nat, arrows in Sub m n, only one type and terms in Raw m

data Val : Set where
  ZeroV : Val
  SuccV : Raw zero → Val
  LamV : Raw one → Val

data _=>_ : Raw zero → Val → Set where
--  subSub  : {m n p : Nat} → {a : Raw p} → {as : Sub n p} → {bs : Sub zero n}
--          → {v : Val}
--          → (a [ as ∘ bs ]) => v
--          → ((a [ as ]) [ bs ])  => v
--  succSub : {m : Nat} → {a : Raw m} → {as : Sub zero m}
--          → (Succ a) [ as ] => SuccV (a [ as ])
--  zeroSub : {m : Nat} → {as : Sub zero m} → Zero [ as ] => ZeroV
  zeroV : Zero => ZeroV
  succV : {a : Raw zero} → Succ a => SuccV a
  recVzero : {base : Raw zero} → {step : Raw (succ (succ zero))}
    → {n : Raw zero} → {v : Val}
    → n => ZeroV → base => v
    → Rec base step n => v
  recVsucc : {base : Raw zero} → {step : Raw (succ (succ zero))}
    → {n a : Raw zero} → {v : Val}
    → n => SuccV a → (step [ < {!< ? , ? >!} , {!!} > ]) => v
    → Rec base step n => v
  beta : {f a : Raw zero} → {b : Raw one} → {v : Val}
    → f => LamV b → b [ < id , a > ] => v
    → App f a => v

data N : Raw zero → Set where
  zeroN : {a : Raw zero} → a => ZeroV → N a
  succN : {a b : Raw zero} → a => SuccV b → N b → N a

SemType : Set₁
SemType = Raw zero → Set

_==>_ : SemType → SemType → SemType
(P ==> Q) f  = (x : Raw zero) → P x → Q (App f x)

-- _⊢_::_ : {n : Nat} → Ctx n → Raw n → Raw n → Set
-- Γ ⊢ a :: A = γ :: Γ → a [ γ ] :: A [ γ ]




