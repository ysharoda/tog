
module PointedZero   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedZero  (A : Set) : Set where 
     field  
      0ᵢ : A  
  
  open PointedZero
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A)  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedZero A1)) (Po2 : (PointedZero A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Po1)) ≡ (0ᵢ Po2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedZero A1)) (Po2 : (PointedZero A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Po1) (0ᵢ Po2))  
  
  data PointedZeroTerm   : Set where 
      0L : PointedZeroTerm  
      
  data ClPointedZeroTerm  (A : Set) : Set where 
      sing : (A → (ClPointedZeroTerm A)) 
      0Cl : (ClPointedZeroTerm A)  
      
  data OpPointedZeroTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedZeroTerm n)) 
      0OL : (OpPointedZeroTerm n)  
      
  data OpPointedZeroTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedZeroTerm2 n A)) 
      sing2 : (A → (OpPointedZeroTerm2 n A)) 
      0OL2 : (OpPointedZeroTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClPointedZeroTerm A) → (ClPointedZeroTerm A)) 
  simplifyCl 0Cl = 0Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPointedZeroTerm n) → (OpPointedZeroTerm n)) 
  simplifyOpB 0OL = 0OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPointedZeroTerm2 n A) → (OpPointedZeroTerm2 n A)) 
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedZero A) → (PointedZeroTerm → A)) 
  evalB Po 0L = (0ᵢ Po)  
  evalCl :  {A : Set} →  ((PointedZero A) → ((ClPointedZeroTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po 0Cl = (0ᵢ Po)  
  evalOpB :  {A : Set} {n : Nat} →  ((PointedZero A) → ((Vec A n) → ((OpPointedZeroTerm n) → A))) 
  evalOpB Po vars (v x1) = (lookup vars x1)  
  evalOpB Po vars 0OL = (0ᵢ Po)  
  evalOp :  {A : Set} {n : Nat} →  ((PointedZero A) → ((Vec A n) → ((OpPointedZeroTerm2 n A) → A))) 
  evalOp Po vars (v2 x1) = (lookup vars x1)  
  evalOp Po vars (sing2 x1) = x1  
  evalOp Po vars 0OL2 = (0ᵢ Po)  
  inductionB :  {P : (PointedZeroTerm → Set)} →  ((P 0L) → ( (x : PointedZeroTerm) → (P x))) 
  inductionB p0l 0L = p0l  
  inductionCl :  {A : Set} {P : ((ClPointedZeroTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → ( (x : (ClPointedZeroTerm A)) → (P x)))) 
  inductionCl psing p0cl (sing x1) = (psing x1)  
  inductionCl psing p0cl 0Cl = p0cl  
  inductionOpB :  {n : Nat} {P : ((OpPointedZeroTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → ( (x : (OpPointedZeroTerm n)) → (P x)))) 
  inductionOpB pv p0ol (v x1) = (pv x1)  
  inductionOpB pv p0ol 0OL = p0ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPointedZeroTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → ( (x : (OpPointedZeroTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 p0ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 0OL2 = p0ol2  
  stageB :  (PointedZeroTerm → (Staged PointedZeroTerm))
  stageB 0L = (Now 0L)  
  stageCl :  {A : Set} →  ((ClPointedZeroTerm A) → (Staged (ClPointedZeroTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageOpB :  {n : Nat} →  ((OpPointedZeroTerm n) → (Staged (OpPointedZeroTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpPointedZeroTerm2 n A) → (Staged (OpPointedZeroTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A)  
  
 