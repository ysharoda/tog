
module RightDistributiveMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightDistributiveMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      rightDistributive : ( {x y z : A} → (op (op y z) x) ≡ (op (op y x) (op z x)))  
  
  open RightDistributiveMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightDistributiveP : ( {xP yP zP : (Prod A A)} → (opP (opP yP zP) xP) ≡ (opP (opP yP xP) (opP zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightDistributiveMagma A1)) (Ri2 : (RightDistributiveMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightDistributiveMagma A1)) (Ri2 : (RightDistributiveMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))  
  
  data RightDistributiveMagmaTerm   : Set where 
      opL : (RightDistributiveMagmaTerm → (RightDistributiveMagmaTerm → RightDistributiveMagmaTerm))  
      
  data ClRightDistributiveMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClRightDistributiveMagmaTerm A)) 
      opCl : ((ClRightDistributiveMagmaTerm A) → ((ClRightDistributiveMagmaTerm A) → (ClRightDistributiveMagmaTerm A)))  
      
  data OpRightDistributiveMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightDistributiveMagmaTerm n)) 
      opOL : ((OpRightDistributiveMagmaTerm n) → ((OpRightDistributiveMagmaTerm n) → (OpRightDistributiveMagmaTerm n)))  
      
  data OpRightDistributiveMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightDistributiveMagmaTerm2 n A)) 
      sing2 : (A → (OpRightDistributiveMagmaTerm2 n A)) 
      opOL2 : ((OpRightDistributiveMagmaTerm2 n A) → ((OpRightDistributiveMagmaTerm2 n A) → (OpRightDistributiveMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClRightDistributiveMagmaTerm A) → (ClRightDistributiveMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpRightDistributiveMagmaTerm n) → (OpRightDistributiveMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpRightDistributiveMagmaTerm2 n A) → (OpRightDistributiveMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightDistributiveMagma A) → (RightDistributiveMagmaTerm → A)) 
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightDistributiveMagma A) → ((ClRightDistributiveMagmaTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((RightDistributiveMagma A) → ((Vec A n) → ((OpRightDistributiveMagmaTerm n) → A))) 
  evalOpB n Ri vars (v x1) = (lookup vars x1)  
  evalOpB n Ri vars (opOL x1 x2) = ((op Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((RightDistributiveMagma A) → ((Vec A n) → ((OpRightDistributiveMagmaTerm2 n A) → A))) 
  evalOp n Ri vars (v2 x1) = (lookup vars x1)  
  evalOp n Ri vars (sing2 x1) = x1  
  evalOp n Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  inductionB :  (P : (RightDistributiveMagmaTerm → Set)) →  (( (x1 x2 : RightDistributiveMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : RightDistributiveMagmaTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClRightDistributiveMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightDistributiveMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClRightDistributiveMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpRightDistributiveMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightDistributiveMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpRightDistributiveMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpRightDistributiveMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightDistributiveMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpRightDistributiveMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (RightDistributiveMagmaTerm → (Staged RightDistributiveMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClRightDistributiveMagmaTerm A) → (Staged (ClRightDistributiveMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpRightDistributiveMagmaTerm n) → (Staged (OpRightDistributiveMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpRightDistributiveMagmaTerm2 n A) → (Staged (OpRightDistributiveMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 