module CZF.AczelV1 where

open import MLTT.MLTT hiding (w)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

V : Set
V = W U T

-- equality as bisimulation, cf isomorphism

_≈_ : V → V → Set
sup a v ≈ sup a' v'
  = (Σ (T a → T a') (λ f → (i : T a) → v i ≈ v' (f i))) ×
    (Σ (T a' → T a) (λ f' → (i' : T a') → v' i' ≈ v (f' i')))

≈-refl : (u : V) → u ≈ u
≈-refl (sup a v) = (( (λ i → i) , (λ i → ≈-refl (v i)) ) , ( (λ i → i) , (λ i → ≈-refl (v i)) ))

≈-sym : (u v : V) → u ≈ v → v ≈ u
≈-sym (sup a v) (sup a' v') (fp , gq) = (gq , fp)

≈-trans : (u u' u'' : V) → u ≈ u' → u' ≈ u'' → u ≈ u''
≈-trans (sup a v) (sup a' v') (sup a'' v'') ((f , p) , (g , q)) ((f' , p') , (g' , q'))
  = (((λ i → f' (f i)) ,
      (λ i → ≈-trans (v i) (v' (f i)) (v'' (f' (f i))) (p i) (p' (f i)))) ,
      ((λ i'' → g (g' i'')) ,
      (λ i'' → ≈-trans (v'' i'') (v' (g' i'')) (v (g (g' i''))) (q' i'') (q (g' i'')))))

-- extensional membership

_∈_ : V → V → Set
u ∈ sup a v = Σ (T a) (λ i → u ≈ v i)

∈-pres : (u u' v : V) → u ≈ u' → u ∈ v → u' ∈ v
∈-pres u u' (sup a v) fq (a₁ , p) = (a₁ , ≈-trans {!!} {!!} {!!} {!!} {!!})


