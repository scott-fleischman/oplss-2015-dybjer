module LF.Introduction where

Id-set : Set → Set
Id-set = λ X → X

id : {X : Set} → X → X
id x = x

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g (f x)

