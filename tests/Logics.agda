module Logics where

-- Propositonal Logic , using function types instead of implication arrows. 
record PropLogic (P : Set) : Set₁ where -- why can't I use Prop instead of P?
  field
   ⊤,⊥  : P
   ~_   : P → P 
   _∧_  : P → P → P 
   _∨_  : P → P → P
   -- removing ded produces an error: P should be a sort, but it isn't 
   -- toy : (p q : P) → (ded : P → Set) → ded (p ⟶ q)
   modusPonens : (p q : P) → (ded : P → Set) → ded p → ((ded p → ded q) → ded q)
   pc1 : (p q : P) → (ded : P → Set) → (ded (~ p) → ded (~ q)) → (ded q → ded p) 
   pl1 : (p q : P) → (ded : P → Set) → ded p → (ded q → ded p)
   pl2 : (p q r : P) → (ded : P → Set) → (ded p → (ded q → ded r)) → ((ded p → ded q) → (ded p → ded r))
   pl3 : (p q : P) → (ded : P → Set) → ded (p ∧ q) → ded p
   pl4 : (p q : P) → (ded : P → Set) → ded (p ∧ q) → ded q
   pl5 : (p q : P) → (ded : P → Set) → ded p → (ded q → (ded (p ∧ q)))
   pl6 : (p q : P) → (ded : P → Set) → ded p → (ded (p ∨ q))
   pl7 : (p q : P) → (ded : P → Set) → ded q → (ded (p ∨ q))
   pl8 : (p q r : P) → (ded : P → Set) → (ded p → ded r) → ((ded q → ded r) → ded (p ∨ q) → ded r)

-- To use ⊡ for modal logic, I had to bring ⟶ back. The problem is that ⊡ expects an input of type P. So when we present the implication as (p → q), its type is no longer P, and therefore we cannot put ⊡ in front of it. 
record ModalLogic (P : Set) : Set₁ where
  field
   ⊤,⊥ : P
   ~_  : P → P 
   _∧_ : P → P → P 
   _∨_ : P → P → P
   _⟶_ : P → P → P 
   ⊡_ : P → P 
   modusPonens : (p q : P) → (ded : P → Set) → ded (p ⟶ ((p ⟶ q) ⟶ q))
   pc1 : (p q : P) → (ded : P → Set) → ded ((~ p) ⟶ (~ q)) → ded (q ⟶ p) 
   pl1 : (p q : P) → (ded : P → Set) → ded (p ⟶ (q ⟶ p))
   pl2 : (p q r : P) → (ded : P → Set) → ded ((p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r)))
   pl3 : (p q : P) → (ded : P → Set) → ded ((p ∧ q) ⟶ p)
   pl4 : (p q : P) → (ded : P → Set) → ded ((p ∧ q) ⟶ q)
   pl5 : (p q : P) → (ded : P → Set) → ded (p ⟶ (q ⟶ (p ∧ q)))
   pl6 : (p q : P) → (ded : P → Set) → ded (p ⟶ (p ∨ q))
   pl7 : (p q : P) → (ded : P → Set) → ded (q ⟶ (p ∨ q))
   pl8 : (p q r : P) → (ded : P → Set) → ded ((p ⟶ r) ⟶ ((q ⟶ r) ⟶ ((p ∨ q) ⟶ r))) 
   distrib : (p q : P) → (ded : P → Set) → ded ((⊡ (p ⟶ q)) ⟶ ((⊡ p) ⟶ (⊡ q)))
   M_axiom : (p : P) → (ded : P → Set) → ded ((⊡ p) ⟶ p)
   four_axiom : (p : P) → (ded : P → Set) → ded ((⊡ p) ⟶ (⊡ (⊡ p)))
   
