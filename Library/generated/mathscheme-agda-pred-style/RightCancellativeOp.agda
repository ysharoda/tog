
module RightCancellativeOp   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightCancellativeOp  (A : Set) (op : (A → (A → A))) (rinv : (A → (A → A))) : Set where 
     field  
      rightCancelOp : ( {x y : A} → (rinv (op y x) x) ≡ y)  
  
  record RightCancellativeOp  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      rinv : (A → (A → A)) 
      isRightCancellativeOp : (IsRightCancellativeOp A op rinv)  
  
  open RightCancellativeOp
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      rinvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightCancelOpP : ( {xP yP : (Prod A A)} → (rinvP (opP yP xP) xP) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightCancellativeOp A1)) (Ri2 : (RightCancellativeOp A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2))) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Ri1) x1 x2)) ≡ ((rinv Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightCancellativeOp A1)) (Ri2 : (RightCancellativeOp A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2))))) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))  
  
  data RightCancellativeOpTerm   : Set where 
      opL : (RightCancellativeOpTerm → (RightCancellativeOpTerm → RightCancellativeOpTerm)) 
      rinvL : (RightCancellativeOpTerm → (RightCancellativeOpTerm → RightCancellativeOpTerm))  
      
  data ClRightCancellativeOpTerm  (A : Set) : Set where 
      sing : (A → (ClRightCancellativeOpTerm A)) 
      opCl : ((ClRightCancellativeOpTerm A) → ((ClRightCancellativeOpTerm A) → (ClRightCancellativeOpTerm A))) 
      rinvCl : ((ClRightCancellativeOpTerm A) → ((ClRightCancellativeOpTerm A) → (ClRightCancellativeOpTerm A)))  
      
  data OpRightCancellativeOpTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightCancellativeOpTerm n)) 
      opOL : ((OpRightCancellativeOpTerm n) → ((OpRightCancellativeOpTerm n) → (OpRightCancellativeOpTerm n))) 
      rinvOL : ((OpRightCancellativeOpTerm n) → ((OpRightCancellativeOpTerm n) → (OpRightCancellativeOpTerm n)))  
      
  data OpRightCancellativeOpTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightCancellativeOpTerm2 n A)) 
      sing2 : (A → (OpRightCancellativeOpTerm2 n A)) 
      opOL2 : ((OpRightCancellativeOpTerm2 n A) → ((OpRightCancellativeOpTerm2 n A) → (OpRightCancellativeOpTerm2 n A))) 
      rinvOL2 : ((OpRightCancellativeOpTerm2 n A) → ((OpRightCancellativeOpTerm2 n A) → (OpRightCancellativeOpTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightCancellativeOpTerm A) → (ClRightCancellativeOpTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (rinvCl x1 x2) = (rinvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightCancellativeOpTerm n) → (OpRightCancellativeOpTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (rinvOL x1 x2) = (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightCancellativeOpTerm2 n A) → (OpRightCancellativeOpTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightCancellativeOp A) → (RightCancellativeOpTerm → A)) 
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (rinvL x1 x2) = ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightCancellativeOp A) → ((ClRightCancellativeOpTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (rinvCl x1 x2) = ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightCancellativeOp A) → ((Vec A n) → ((OpRightCancellativeOpTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (opOL x1 x2) = ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars (rinvOL x1 x2) = ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightCancellativeOp A) → ((Vec A n) → ((OpRightCancellativeOpTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars (rinvOL2 x1 x2) = ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightCancellativeOpTerm → Set)} →  (( (x1 x2 : RightCancellativeOpTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 x2 : RightCancellativeOpTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : RightCancellativeOpTerm) → (P x)))) 
  inductionB popl prinvl (opL x1 x2) = (popl _ _ (inductionB popl prinvl x1) (inductionB popl prinvl x2))  
  inductionB popl prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB popl prinvl x1) (inductionB popl prinvl x2))  
  inductionCl :  {A : Set} {P : ((ClRightCancellativeOpTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightCancellativeOpTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 x2 : (ClRightCancellativeOpTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClRightCancellativeOpTerm A)) → (P x))))) 
  inductionCl psing popcl prinvcl (sing x1) = (psing x1)  
  inductionCl psing popcl prinvcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl prinvcl x1) (inductionCl psing popcl prinvcl x2))  
  inductionCl psing popcl prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl psing popcl prinvcl x1) (inductionCl psing popcl prinvcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightCancellativeOpTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightCancellativeOpTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 x2 : (OpRightCancellativeOpTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpRightCancellativeOpTerm n)) → (P x))))) 
  inductionOpB pv popol prinvol (v x1) = (pv x1)  
  inductionOpB pv popol prinvol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol prinvol x1) (inductionOpB pv popol prinvol x2))  
  inductionOpB pv popol prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB pv popol prinvol x1) (inductionOpB pv popol prinvol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightCancellativeOpTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightCancellativeOpTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 x2 : (OpRightCancellativeOpTerm2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpRightCancellativeOpTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 prinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 prinvol2 x2))  
  inductionOp pv2 psing2 popol2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp pv2 psing2 popol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 prinvol2 x2))  
  stageB :  (RightCancellativeOpTerm → (Staged RightCancellativeOpTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightCancellativeOpTerm A) → (Staged (ClRightCancellativeOpTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightCancellativeOpTerm n) → (Staged (OpRightCancellativeOpTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightCancellativeOpTerm2 n A) → (Staged (OpRightCancellativeOpTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 