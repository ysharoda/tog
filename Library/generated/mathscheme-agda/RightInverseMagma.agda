
module RightInverseMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightInverseMagma  (A : Set) : Set where 
     field  
      rinv : (A → (A → A))  
  
  open RightInverseMagma
  record Sig  (AS : Set) : Set where 
     field  
      rinvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      rinvP : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightInverseMagma A1)) (Ri2 : (RightInverseMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Ri1) x1 x2)) ≡ ((rinv Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightInverseMagma A1)) (Ri2 : (RightInverseMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))  
  
  data RightInverseMagmaTerm   : Set where 
      rinvL : (RightInverseMagmaTerm → (RightInverseMagmaTerm → RightInverseMagmaTerm))  
      
  data ClRightInverseMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClRightInverseMagmaTerm A)) 
      rinvCl : ((ClRightInverseMagmaTerm A) → ((ClRightInverseMagmaTerm A) → (ClRightInverseMagmaTerm A)))  
      
  data OpRightInverseMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightInverseMagmaTerm n)) 
      rinvOL : ((OpRightInverseMagmaTerm n) → ((OpRightInverseMagmaTerm n) → (OpRightInverseMagmaTerm n)))  
      
  data OpRightInverseMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightInverseMagmaTerm2 n A)) 
      sing2 : (A → (OpRightInverseMagmaTerm2 n A)) 
      rinvOL2 : ((OpRightInverseMagmaTerm2 n A) → ((OpRightInverseMagmaTerm2 n A) → (OpRightInverseMagmaTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightInverseMagmaTerm A) → (ClRightInverseMagmaTerm A)) 
  simplifyCl (rinvCl x1 x2) = (rinvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightInverseMagmaTerm n) → (OpRightInverseMagmaTerm n)) 
  simplifyOpB (rinvOL x1 x2) = (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightInverseMagmaTerm2 n A) → (OpRightInverseMagmaTerm2 n A)) 
  simplifyOp (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightInverseMagma A) → (RightInverseMagmaTerm → A)) 
  evalB Ri (rinvL x1 x2) = ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightInverseMagma A) → ((ClRightInverseMagmaTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (rinvCl x1 x2) = ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightInverseMagma A) → ((Vec A n) → ((OpRightInverseMagmaTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (rinvOL x1 x2) = ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightInverseMagma A) → ((Vec A n) → ((OpRightInverseMagmaTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (rinvOL2 x1 x2) = ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightInverseMagmaTerm → Set)} →  (( (x1 x2 : RightInverseMagmaTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : RightInverseMagmaTerm) → (P x))) 
  inductionB prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB prinvl x1) (inductionB prinvl x2))  
  inductionCl :  {A : Set} {P : ((ClRightInverseMagmaTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightInverseMagmaTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClRightInverseMagmaTerm A)) → (P x)))) 
  inductionCl psing prinvcl (sing x1) = (psing x1)  
  inductionCl psing prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl psing prinvcl x1) (inductionCl psing prinvcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightInverseMagmaTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightInverseMagmaTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpRightInverseMagmaTerm n)) → (P x)))) 
  inductionOpB pv prinvol (v x1) = (pv x1)  
  inductionOpB pv prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB pv prinvol x1) (inductionOpB pv prinvol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightInverseMagmaTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightInverseMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpRightInverseMagmaTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp pv2 psing2 prinvol2 x1) (inductionOp pv2 psing2 prinvol2 x2))  
  stageB :  (RightInverseMagmaTerm → (Staged RightInverseMagmaTerm))
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightInverseMagmaTerm A) → (Staged (ClRightInverseMagmaTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightInverseMagmaTerm n) → (Staged (OpRightInverseMagmaTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightInverseMagmaTerm2 n A) → (Staged (OpRightInverseMagmaTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 