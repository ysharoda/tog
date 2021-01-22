
module PointedOne   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointedOne  (A : Set) (1ᵢ : A) : Set where 
    
  record PointedOne  (A : Set) : Set where 
     field  
      1ᵢ : A 
      isPointedOne : (IsPointedOne A 1ᵢ)  
  
  open PointedOne
  record Sig  (AS : Set) : Set where 
     field  
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      1P : (Prod A A)  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedOne A1)) (Po2 : (PointedOne A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-1 : (hom (1ᵢ Po1)) ≡ (1ᵢ Po2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedOne A1)) (Po2 : (PointedOne A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-1 : (interp (1ᵢ Po1) (1ᵢ Po2))  
  
  data PointedOneTerm   : Set where 
      1L : PointedOneTerm  
      
  data ClPointedOneTerm  (A : Set) : Set where 
      sing : (A → (ClPointedOneTerm A)) 
      1Cl : (ClPointedOneTerm A)  
      
  data OpPointedOneTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedOneTerm n)) 
      1OL : (OpPointedOneTerm n)  
      
  data OpPointedOneTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedOneTerm2 n A)) 
      sing2 : (A → (OpPointedOneTerm2 n A)) 
      1OL2 : (OpPointedOneTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClPointedOneTerm A) → (ClPointedOneTerm A)) 
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPointedOneTerm n) → (OpPointedOneTerm n)) 
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPointedOneTerm2 n A) → (OpPointedOneTerm2 n A)) 
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedOne A) → (PointedOneTerm → A)) 
  evalB Po 1L = (1ᵢ Po)  
  evalCl :  {A : Set} →  ((PointedOne A) → ((ClPointedOneTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po 1Cl = (1ᵢ Po)  
  evalOpB :  {A : Set} {n : Nat} →  ((PointedOne A) → ((Vec A n) → ((OpPointedOneTerm n) → A))) 
  evalOpB Po vars (v x1) = (lookup vars x1)  
  evalOpB Po vars 1OL = (1ᵢ Po)  
  evalOp :  {A : Set} {n : Nat} →  ((PointedOne A) → ((Vec A n) → ((OpPointedOneTerm2 n A) → A))) 
  evalOp Po vars (v2 x1) = (lookup vars x1)  
  evalOp Po vars (sing2 x1) = x1  
  evalOp Po vars 1OL2 = (1ᵢ Po)  
  inductionB :  {P : (PointedOneTerm → Set)} →  ((P 1L) → ( (x : PointedOneTerm) → (P x))) 
  inductionB p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClPointedOneTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 1Cl) → ( (x : (ClPointedOneTerm A)) → (P x)))) 
  inductionCl psing p1cl (sing x1) = (psing x1)  
  inductionCl psing p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpPointedOneTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 1OL) → ( (x : (OpPointedOneTerm n)) → (P x)))) 
  inductionOpB pv p1ol (v x1) = (pv x1)  
  inductionOpB pv p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPointedOneTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 1OL2) → ( (x : (OpPointedOneTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p1ol2 1OL2 = p1ol2  
  stageB :  (PointedOneTerm → (Staged PointedOneTerm))
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClPointedOneTerm A) → (Staged (ClPointedOneTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpPointedOneTerm n) → (Staged (OpPointedOneTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpPointedOneTerm2 n A) → (Staged (OpPointedOneTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      1T : (Repr A)  
  
 