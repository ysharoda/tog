
module InverseUnaryOperation   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InverseUnaryOperation  (A : Set) : Set where 
     field  
      inv : (A → A)  
  
  open InverseUnaryOperation
  record Sig  (AS : Set) : Set where 
     field  
      invS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      invP : ((Prod A A) → (Prod A A))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InverseUnaryOperation A1)) (In2 : (InverseUnaryOperation A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-inv : ( {x1 : A1} → (hom ((inv In1) x1)) ≡ ((inv In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InverseUnaryOperation A1)) (In2 : (InverseUnaryOperation A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv In1) x1) ((inv In2) y1))))  
  
  data InverseUnaryOperationTerm   : Set where 
      invL : (InverseUnaryOperationTerm → InverseUnaryOperationTerm)  
      
  data ClInverseUnaryOperationTerm  (A : Set) : Set where 
      sing : (A → (ClInverseUnaryOperationTerm A)) 
      invCl : ((ClInverseUnaryOperationTerm A) → (ClInverseUnaryOperationTerm A))  
      
  data OpInverseUnaryOperationTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInverseUnaryOperationTerm n)) 
      invOL : ((OpInverseUnaryOperationTerm n) → (OpInverseUnaryOperationTerm n))  
      
  data OpInverseUnaryOperationTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInverseUnaryOperationTerm2 n A)) 
      sing2 : (A → (OpInverseUnaryOperationTerm2 n A)) 
      invOL2 : ((OpInverseUnaryOperationTerm2 n A) → (OpInverseUnaryOperationTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClInverseUnaryOperationTerm A) → (ClInverseUnaryOperationTerm A)) 
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInverseUnaryOperationTerm n) → (OpInverseUnaryOperationTerm n)) 
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInverseUnaryOperationTerm2 n A) → (OpInverseUnaryOperationTerm2 n A)) 
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InverseUnaryOperation A) → (InverseUnaryOperationTerm → A)) 
  evalB In (invL x1) = ((inv In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InverseUnaryOperation A) → ((ClInverseUnaryOperationTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (invCl x1) = ((inv In) (evalCl In x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((InverseUnaryOperation A) → ((Vec A n) → ((OpInverseUnaryOperationTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (invOL x1) = ((inv In) (evalOpB In vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((InverseUnaryOperation A) → ((Vec A n) → ((OpInverseUnaryOperationTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (invOL2 x1) = ((inv In) (evalOp In vars x1))  
  inductionB :  {P : (InverseUnaryOperationTerm → Set)} →  (( (x1 : InverseUnaryOperationTerm) → ((P x1) → (P (invL x1)))) → ( (x : InverseUnaryOperationTerm) → (P x))) 
  inductionB pinvl (invL x1) = (pinvl _ (inductionB pinvl x1))  
  inductionCl :  {A : Set} {P : ((ClInverseUnaryOperationTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInverseUnaryOperationTerm A)) → ((P x1) → (P (invCl x1)))) → ( (x : (ClInverseUnaryOperationTerm A)) → (P x)))) 
  inductionCl psing pinvcl (sing x1) = (psing x1)  
  inductionCl psing pinvcl (invCl x1) = (pinvcl _ (inductionCl psing pinvcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpInverseUnaryOperationTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInverseUnaryOperationTerm n)) → ((P x1) → (P (invOL x1)))) → ( (x : (OpInverseUnaryOperationTerm n)) → (P x)))) 
  inductionOpB pv pinvol (v x1) = (pv x1)  
  inductionOpB pv pinvol (invOL x1) = (pinvol _ (inductionOpB pv pinvol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInverseUnaryOperationTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInverseUnaryOperationTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → ( (x : (OpInverseUnaryOperationTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 pinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pinvol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 pinvol2 x1))  
  stageB :  (InverseUnaryOperationTerm → (Staged InverseUnaryOperationTerm))
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClInverseUnaryOperationTerm A) → (Staged (ClInverseUnaryOperationTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpInverseUnaryOperationTerm n) → (Staged (OpInverseUnaryOperationTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInverseUnaryOperationTerm2 n A) → (Staged (OpInverseUnaryOperationTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      invT : ((Repr A) → (Repr A))  
  
 