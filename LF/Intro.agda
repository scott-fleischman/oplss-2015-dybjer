module LF.Intro where

I-Set : Set → Set
I-Set = λ (X : Set) → X

I : {X : Set} → X → X
I x = x

K : {X Y : Set} → X → Y → X
K {X = A} {Y = B} x _ = x

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g (f {!x!})


