
module RightBiMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightBiMagma  (A : Set) (op : (A → (A → A))) (rinv : (A → (A → A))) : Set where 
    
  record RightBiMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      rinv : (A → (A → A)) 
      isRightBiMagma : (IsRightBiMagma A op rinv)  
  
  open RightBiMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      rinvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rinvP : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightBiMagma A1)) (Ri2 : (RightBiMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2))) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Ri1) x1 x2)) ≡ ((rinv Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightBiMagma A1)) (Ri2 : (RightBiMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2))))) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))  
  
  data RightBiMagmaTerm   : Set where 
      opL : (RightBiMagmaTerm → (RightBiMagmaTerm → RightBiMagmaTerm)) 
      rinvL : (RightBiMagmaTerm → (RightBiMagmaTerm → RightBiMagmaTerm))  
      
  data ClRightBiMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClRightBiMagmaTerm A)) 
      opCl : ((ClRightBiMagmaTerm A) → ((ClRightBiMagmaTerm A) → (ClRightBiMagmaTerm A))) 
      rinvCl : ((ClRightBiMagmaTerm A) → ((ClRightBiMagmaTerm A) → (ClRightBiMagmaTerm A)))  
      
  data OpRightBiMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightBiMagmaTerm n)) 
      opOL : ((OpRightBiMagmaTerm n) → ((OpRightBiMagmaTerm n) → (OpRightBiMagmaTerm n))) 
      rinvOL : ((OpRightBiMagmaTerm n) → ((OpRightBiMagmaTerm n) → (OpRightBiMagmaTerm n)))  
      
  data OpRightBiMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightBiMagmaTerm2 n A)) 
      sing2 : (A → (OpRightBiMagmaTerm2 n A)) 
      opOL2 : ((OpRightBiMagmaTerm2 n A) → ((OpRightBiMagmaTerm2 n A) → (OpRightBiMagmaTerm2 n A))) 
      rinvOL2 : ((OpRightBiMagmaTerm2 n A) → ((OpRightBiMagmaTerm2 n A) → (OpRightBiMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClRightBiMagmaTerm A) → (ClRightBiMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (rinvCl x1 x2) = (rinvCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpRightBiMagmaTerm n) → (OpRightBiMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (rinvOL x1 x2) = (rinvOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpRightBiMagmaTerm2 n A) → (OpRightBiMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightBiMagma A) → (RightBiMagmaTerm → A)) 
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (rinvL x1 x2) = ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightBiMagma A) → ((ClRightBiMagmaTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (rinvCl x1 x2) = ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((RightBiMagma A) → ((Vec A n) → ((OpRightBiMagmaTerm n) → A))) 
  evalOpB n Ri vars (v x1) = (lookup vars x1)  
  evalOpB n Ri vars (opOL x1 x2) = ((op Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOpB n Ri vars (rinvOL x1 x2) = ((rinv Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((RightBiMagma A) → ((Vec A n) → ((OpRightBiMagmaTerm2 n A) → A))) 
  evalOp n Ri vars (v2 x1) = (lookup vars x1)  
  evalOp n Ri vars (sing2 x1) = x1  
  evalOp n Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  evalOp n Ri vars (rinvOL2 x1 x2) = ((rinv Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  inductionB :  (P : (RightBiMagmaTerm → Set)) →  (( (x1 x2 : RightBiMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 x2 : RightBiMagmaTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : RightBiMagmaTerm) → (P x)))) 
  inductionB p popl prinvl (opL x1 x2) = (popl _ _ (inductionB p popl prinvl x1) (inductionB p popl prinvl x2))  
  inductionB p popl prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB p popl prinvl x1) (inductionB p popl prinvl x2))  
  inductionCl :  (A : Set) (P : ((ClRightBiMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightBiMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 x2 : (ClRightBiMagmaTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClRightBiMagmaTerm A)) → (P x))))) 
  inductionCl _ p psing popcl prinvcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl prinvcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl prinvcl x1) (inductionCl _ p psing popcl prinvcl x2))  
  inductionCl _ p psing popcl prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl _ p psing popcl prinvcl x1) (inductionCl _ p psing popcl prinvcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpRightBiMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightBiMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 x2 : (OpRightBiMagmaTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpRightBiMagmaTerm n)) → (P x))))) 
  inductionOpB _ p pv popol prinvol (v x1) = (pv x1)  
  inductionOpB _ p pv popol prinvol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol prinvol x1) (inductionOpB _ p pv popol prinvol x2))  
  inductionOpB _ p pv popol prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB _ p pv popol prinvol x1) (inductionOpB _ p pv popol prinvol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpRightBiMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightBiMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 x2 : (OpRightBiMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpRightBiMagmaTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 popol2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 prinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 prinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 prinvol2 x2))  
  stageB :  (RightBiMagmaTerm → (Staged RightBiMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClRightBiMagmaTerm A) → (Staged (ClRightBiMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpRightBiMagmaTerm n) → (Staged (OpRightBiMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpRightBiMagmaTerm2 n A) → (Staged (OpRightBiMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 