module IR.McCarthy91 where

open import IType.Nat
open import IType.Bool

-- McCarthy's 91-function, a nested recursive function

{-# NON_TERMINATING #-}
mc91 : Nat → Nat
mc91 n = if (n < 101) then mc91 (mc91 (n + 11)) else (n - 10)

-- The Bove-Capretta method yields an inductive-recursive function

data D : Nat → Set
mc91bc : (n : Nat) → D n → Nat

data D where
  base : (n : Nat)
    → So (¬ (n < 101))
    → D n
  nest : (n : Nat)
    → So (n < 101)
    → (p : D (n + 11))
    → D (mc91bc (n + 11) p)
    → D n

mc91bc n (base .n x)     = n - 10
mc91bc n (nest .n x p q) = mc91bc (mc91bc (n + 11) p) q


module TestD where
  open import MLTT.PropositionalLogic hiding (¬)

  d100 : D 100
  d100 = nest 100 ⊤-intro (base 111 ⊤-intro) (base 101 ⊤-intro)

  d99 : D 99
  d99 = nest 99 ⊤-intro (base 110 ⊤-intro) d100

  d98 : D 98
  d98 = nest 98 ⊤-intro (base 109 ⊤-intro) d99

  d97 : D 97
  d97 = nest 97 ⊤-intro (base 108 ⊤-intro) d98

  d96 : D 96
  d96 = nest 96 ⊤-intro (base 107 ⊤-intro) d97

  d95 : D 95
  d95 = nest 95 ⊤-intro (base 106 ⊤-intro) d96

  d94 : D 94
  d94 = nest 94 ⊤-intro (base 105 ⊤-intro) d95

  d93 : D 93
  d93 = nest 93 ⊤-intro (base 104 ⊤-intro) d94

  d92 : D 92
  d92 = nest 92 ⊤-intro (base 103 ⊤-intro) d93

  d91 : D 91
  d91 = nest 91 ⊤-intro (base 102 ⊤-intro) d92

  d88 : D 88
  d88 = nest 88 ⊤-intro d99 d91

  d77 : D 77
  d77 = nest 77 ⊤-intro d88 d91

  d66 : D 66
  d66 = nest 66 ⊤-intro d77 d91

  d55 : D 55
  d55 = nest 55 ⊤-intro d66 d91

  d44 : D 44
  d44 = nest 44 ⊤-intro d55 d91

  d33 : D 33
  d33 = nest 33 ⊤-intro d44 d91

  d22 : D 22
  d22 = nest 22 ⊤-intro d33 d91

  d11 : D 11
  d11 = nest 11 ⊤-intro d22 d91

  d0 : D 0
  d0 = nest zero ⊤-intro d11 d91


-- Relation implementation

data Mc91 : Nat → Nat → Set where
  base : (n : Nat)
    → So (¬ (n < 101))
    → Mc91 n (n - 10)
  nest : {n m r : Nat}
    → Mc91 (n + 11) m
    → Mc91 m r
    → Mc91 n r

module TestMc91 where
  open import MLTT.PropositionalLogic hiding (¬)

  t110 : Mc91 110 100
  t110 = base 110 ⊤-intro

  t100 : Mc91 100 91
  t100 = nest (base 111 ⊤-intro) (base 101 ⊤-intro)

  t99 : Mc91 99 91
  t99 = nest t110 t100

  t98 : Mc91 98 91
  t98 = nest (base 109 ⊤-intro) t99

  t97 : Mc91 97 91
  t97 = nest (base 108 ⊤-intro) t98

  t96 : Mc91 96 91
  t96 = nest (base 107 ⊤-intro) t97

  t95 : Mc91 95 91
  t95 = nest (base 106 ⊤-intro) t96

  t94 : Mc91 94 91
  t94 = nest (base 105 ⊤-intro) t95

  t93 : Mc91 93 91
  t93 = nest (base 104 ⊤-intro) t94

  t92 : Mc91 92 91
  t92 = nest (base 103 ⊤-intro) t93

  t91 : Mc91 91 91
  t91 = nest (base 102 ⊤-intro) t92

  t88 : Mc91 88 91
  t88 = nest t99 t91

  t77 : Mc91 77 91
  t77 = nest t88 t91

  t66 : Mc91 66 91
  t66 = nest t77 t91

  t55 : Mc91 55 91
  t55 = nest t66 t91

  t44 : Mc91 44 91
  t44 = nest t55 t91

  t33 : Mc91 33 91
  t33 = nest t44 t91

  t22 : Mc91 22 91
  t22 = nest t33 t91

  t11 : Mc91 11 91
  t11 = nest t22 t91

  t0 : Mc91 0 91
  t0 = nest t11 t91
