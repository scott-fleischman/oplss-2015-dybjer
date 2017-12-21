module LambdaStructure2 where

open import Nat
open import Fin

-- the set of n-place function following Aczel

-- note not the LF-version of type theory

data F : Nat → Set where
  var   : {n : Nat} → Fin n → F n
  _#_   : {n : Nat} → F n → F n → F n
  lam   : {n : Nat} → F (succ n) → F n
  pi    : {n : Nat} → F n → F (succ n) → F n
  set   : {n : Nat} → F n
  zeroF : {n : Nat} → F n
  succF : {n : Nat} → F n
  recF  : {n : Nat} → F n
  NF    : {n : Nat} → F n

infixl 50 _#_

data Val : Set where
  lamV  : F one → Val
  piV   : F zero → F one → Val
  setV  : Val
  zeroV : Val
  succV : F zero → Val
  NV    : Val

postulate
  _[_] : F one → F zero → F zero

data _=>_ : F zero → Val → Set where
  β : {c a : F zero} → {b : F one} → {v : Val}
    → c => lamV b → b [ a ] => v → c # a => v
  lamVal : {b : F one} → lam b => lamV b
  piVal : {a : F zero} → {b : F one} → pi a b => piV a b
  setVal : set => setV
  zeroVal : zeroF => zeroV
  succVal : {a : F zero} → succF # a => succV a
  reczeroVal : {n d e : F zero} → {v : Val}
    → n => zeroV
    → d => v
    → recF # d # e # n => v
  recsuccVal : {m n d e : F zero} → {v : Val}
    → n => succV m
    → e # m # (recF # d # e # m) => v
    → recF # d # e # n => v
  NVal : NF => NV

data isN : F zero → Set where
  zeroN : {a : F zero} → a => zeroV → isN a
  succN : {a b : F zero} → a => succV b → isN b → isN a

-- an inductive-recursive definition!

mutual
  data isset : F zero → Set where    
    piset : {A : F zero} → (B : F zero) → (C : F one)
      → A => piV B C
      → (p : isset B)
      → ((x : F zero) → isel x B p → isset (C [ x ]))
      → isset A
    Nset : {A : F zero} → A => NV → isset A
    
  isel : F zero → (A : F zero) → isset A → Set
  isel a A (piset B C d p q) = (x : F zero) → (y : isel x B p)
    → isel (a # x) (C [ x ]) (q x y)
  isel a A (Nset x) = isN a

mutual 
  data isTy : F zero → Set where
    piTy : {A : F zero} → (B : F zero) → (C : F one)
      → A => piV B C
      → (p : isTy B)
      → ((x : F zero) → isTm x B p → isTy (C [ x ]))
      → isTy A
    setTy : {A : F zero}
      → A => setV
      → isTy A
    NTy : {A : F zero}
      → A => NV
      → isTy A

  isTm : F zero → (A : F zero) → isTy A → Set
  isTm a A (piTy B C d p q) = (b : F zero) → (y : isTm b B p)
    → isTm (a # b) (C [ b ]) (q b y)
  isTm a A (setTy x) = isset a
  isTm a A (NTy x) = isN a

-- Typing open terms, meaning of hypothetical judgments. The meaning of
-- x : A ⊢ b : B is the same as λ x → b : (x : A) → B, etc

-- Rqw contexts

data Ctx : Nat → Set where
  []  : Ctx zero
  _,_ : {n : Nat} → Ctx n → F n → Ctx (succ n)

-- Raw environments

open import Vector renaming (_::_ to cons)

Env : Nat → Set
Env n = Vect (F zero) n

postulate
  inst : {n : Nat} → F n → Env n → F zero
  
mutual
  data isCtx : {n : Nat} → Ctx n → Set where
    nil-ctx : isCtx []
    cons-ctx : {n : Nat} → {Γ : Ctx n} → {A : F n}
      → (p : isCtx Γ) → isTyCtx Γ p A → isCtx (Γ , A)

  isTyCtx : {n : Nat} → (Γ : Ctx n) → isCtx Γ → F n → Set
  isTyCtx {n} Γ p A = (ρ : Env n) → isEnvCtx Γ p ρ → isTy (inst A ρ)

  data isEnvCtx : {n : Nat} → (Γ : Ctx n) → isCtx Γ → (ρ : Env n) → Set where
    nil-env : isEnvCtx [] nil-ctx []
    cons-env : {n : Nat} → (Γ : Ctx n) → isCtx Γ → (A : F n) → isTyCtx → (ρ : Env n) → ? → isEnvCtx (Γ , A) ? (cons ρ a)
    
  isTmTyCtx : {n : Nat}
    → (Γ : Ctx n) → (p : isCtx Γ) → (A : F n) → isTyCtx Γ p A → F n → Set 
  isTmTyCtx {n} Γ p A q a = (ρ : Env n) → isEnvCtx Γ p ρ → isTm (inst a ρ) (inst A ρ) {!!}

--  lemma : (A : F n) → (ρ : Env n) → isTyCtx  isTy (inst A ρ)

  
-- Γ ⊢ a :: A = (ρ : Env n) → ρ fits Γ → inst a ρ :: inst A ρ



-- isEnv : {n : Nat} → Vect (F zero)

-- isTyCtx : {n : Nat} → (A : F n) → (Γ : Ctx n) → Set
-- isTyCtx {n} A Γ = (γ : Vect (F zero) n) → isSub γ Γ → isTy (A [ γ ])

-- IsTmCtx


  
   
