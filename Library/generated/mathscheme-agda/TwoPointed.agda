
module TwoPointed   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record TwoPointed  (A : Set) : Set where 
     field  
      e1 : A 
      e2 : A  
  
  open TwoPointed
  record Sig  (AS : Set) : Set where 
     field  
      e1S : AS 
      e2S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      e1P : (Prod A A) 
      e2P : (Prod A A)  
  
  record Hom  {A1 : Set} {A2 : Set} (Tw1 : (TwoPointed A1)) (Tw2 : (TwoPointed A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e1 : (hom (e1 Tw1)) ≡ (e1 Tw2) 
      pres-e2 : (hom (e2 Tw1)) ≡ (e2 Tw2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Tw1 : (TwoPointed A1)) (Tw2 : (TwoPointed A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e1 : (interp (e1 Tw1) (e1 Tw2)) 
      interp-e2 : (interp (e2 Tw1) (e2 Tw2))  
  
  data TwoPointedTerm   : Set where 
      e1L : TwoPointedTerm 
      e2L : TwoPointedTerm  
      
  data ClTwoPointedTerm  (A : Set) : Set where 
      sing : (A → (ClTwoPointedTerm A)) 
      e1Cl : (ClTwoPointedTerm A) 
      e2Cl : (ClTwoPointedTerm A)  
      
  data OpTwoPointedTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpTwoPointedTerm n)) 
      e1OL : (OpTwoPointedTerm n) 
      e2OL : (OpTwoPointedTerm n)  
      
  data OpTwoPointedTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpTwoPointedTerm2 n A)) 
      sing2 : (A → (OpTwoPointedTerm2 n A)) 
      e1OL2 : (OpTwoPointedTerm2 n A) 
      e2OL2 : (OpTwoPointedTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClTwoPointedTerm A) → (ClTwoPointedTerm A)) 
  simplifyCl _ e1Cl = e1Cl  
  simplifyCl _ e2Cl = e2Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpTwoPointedTerm n) → (OpTwoPointedTerm n)) 
  simplifyOpB _ e1OL = e1OL  
  simplifyOpB _ e2OL = e2OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpTwoPointedTerm2 n A) → (OpTwoPointedTerm2 n A)) 
  simplifyOp _ _ e1OL2 = e1OL2  
  simplifyOp _ _ e2OL2 = e2OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((TwoPointed A) → (TwoPointedTerm → A)) 
  evalB Tw e1L = (e1 Tw)  
  evalB Tw e2L = (e2 Tw)  
  evalCl :  {A : Set} →  ((TwoPointed A) → ((ClTwoPointedTerm A) → A)) 
  evalCl Tw (sing x1) = x1  
  evalCl Tw e1Cl = (e1 Tw)  
  evalCl Tw e2Cl = (e2 Tw)  
  evalOpB :  {A : Set} (n : Nat) →  ((TwoPointed A) → ((Vec A n) → ((OpTwoPointedTerm n) → A))) 
  evalOpB n Tw vars (v x1) = (lookup vars x1)  
  evalOpB n Tw vars e1OL = (e1 Tw)  
  evalOpB n Tw vars e2OL = (e2 Tw)  
  evalOp :  {A : Set} (n : Nat) →  ((TwoPointed A) → ((Vec A n) → ((OpTwoPointedTerm2 n A) → A))) 
  evalOp n Tw vars (v2 x1) = (lookup vars x1)  
  evalOp n Tw vars (sing2 x1) = x1  
  evalOp n Tw vars e1OL2 = (e1 Tw)  
  evalOp n Tw vars e2OL2 = (e2 Tw)  
  inductionB :  (P : (TwoPointedTerm → Set)) →  ((P e1L) → ((P e2L) → ( (x : TwoPointedTerm) → (P x)))) 
  inductionB p pe1l pe2l e1L = pe1l  
  inductionB p pe1l pe2l e2L = pe2l  
  inductionCl :  (A : Set) (P : ((ClTwoPointedTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P e1Cl) → ((P e2Cl) → ( (x : (ClTwoPointedTerm A)) → (P x))))) 
  inductionCl _ p psing pe1cl pe2cl (sing x1) = (psing x1)  
  inductionCl _ p psing pe1cl pe2cl e1Cl = pe1cl  
  inductionCl _ p psing pe1cl pe2cl e2Cl = pe2cl  
  inductionOpB :  (n : Nat) (P : ((OpTwoPointedTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P e1OL) → ((P e2OL) → ( (x : (OpTwoPointedTerm n)) → (P x))))) 
  inductionOpB _ p pv pe1ol pe2ol (v x1) = (pv x1)  
  inductionOpB _ p pv pe1ol pe2ol e1OL = pe1ol  
  inductionOpB _ p pv pe1ol pe2ol e2OL = pe2ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpTwoPointedTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P e1OL2) → ((P e2OL2) → ( (x : (OpTwoPointedTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 pe1ol2 pe2ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pe1ol2 pe2ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pe1ol2 pe2ol2 e1OL2 = pe1ol2  
  inductionOp _ _ p pv2 psing2 pe1ol2 pe2ol2 e2OL2 = pe2ol2  
  stageB :  (TwoPointedTerm → (Staged TwoPointedTerm))
  stageB e1L = (Now e1L)  
  stageB e2L = (Now e2L)  
  stageCl :  (A : Set) →  ((ClTwoPointedTerm A) → (Staged (ClTwoPointedTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ e1Cl = (Now e1Cl)  
  stageCl _ e2Cl = (Now e2Cl)  
  stageOpB :  (n : Nat) →  ((OpTwoPointedTerm n) → (Staged (OpTwoPointedTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ e1OL = (Now e1OL)  
  stageOpB _ e2OL = (Now e2OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpTwoPointedTerm2 n A) → (Staged (OpTwoPointedTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ e1OL2 = (Now e1OL2)  
  stageOp _ _ e2OL2 = (Now e2OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      e1T : (Repr A) 
      e2T : (Repr A)  
  
 