-- Church's simple theory of types 1940
-- see eg Stanford Encyclopedia of Philosophy
-- "Church's Type Theory" by Peter Andrews

module LF.HOL where

postulate

-- base types

  i : Set -- the type of individuals
  o : Set -- the type of propositions
  
-- logical constants

  ~ : o → o
  _∨_ : o → o → o
  Π : (α : Set) → (α → o) → o -- typed universal quantifier (hol!)
  ι : (α : Set) → (α → o) → α -- description operator
  ∃! : (α : Set) → (α → o) → o -- unique existence (definable in terms of other primitives)
  
-- theoremhood, a property of propositions

  T : o → Set
  
-- examples of axioms (there are more!)

  excluded-middle : (φ : o)
    → T (φ ∨ ~ φ)
  axiom-of-description :  (α : Set) → (φ : α → o)
    → T (∃! α φ)
    → T (φ (ι α φ))
    
-- Exercise: implement the other axioms of HOL (see Andrews)!
  
