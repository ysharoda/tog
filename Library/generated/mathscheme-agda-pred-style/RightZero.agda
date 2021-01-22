
module RightZero   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightZero  (A : Set) (e : A) (op : (A → (A → A))) : Set where 
     field  
      rightZero_op_e : ( {x : A} → (op x e) ≡ e)  
  
  record RightZero  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      isRightZero : (IsRightZero A e op)  
  
  open RightZero
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightZero_op_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightZero A1)) (Ri2 : (RightZero A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Ri1)) ≡ (e Ri2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightZero A1)) (Ri2 : (RightZero A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Ri1) (e Ri2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))  
  
  data RightZeroTerm   : Set where 
      eL : RightZeroTerm 
      opL : (RightZeroTerm → (RightZeroTerm → RightZeroTerm))  
      
  data ClRightZeroTerm  (A : Set) : Set where 
      sing : (A → (ClRightZeroTerm A)) 
      eCl : (ClRightZeroTerm A) 
      opCl : ((ClRightZeroTerm A) → ((ClRightZeroTerm A) → (ClRightZeroTerm A)))  
      
  data OpRightZeroTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightZeroTerm n)) 
      eOL : (OpRightZeroTerm n) 
      opOL : ((OpRightZeroTerm n) → ((OpRightZeroTerm n) → (OpRightZeroTerm n)))  
      
  data OpRightZeroTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightZeroTerm2 n A)) 
      sing2 : (A → (OpRightZeroTerm2 n A)) 
      eOL2 : (OpRightZeroTerm2 n A) 
      opOL2 : ((OpRightZeroTerm2 n A) → ((OpRightZeroTerm2 n A) → (OpRightZeroTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightZeroTerm A) → (ClRightZeroTerm A)) 
  simplifyCl eCl = eCl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightZeroTerm n) → (OpRightZeroTerm n)) 
  simplifyOpB eOL = eOL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightZeroTerm2 n A) → (OpRightZeroTerm2 n A)) 
  simplifyOp eOL2 = eOL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightZero A) → (RightZeroTerm → A)) 
  evalB Ri eL = (e Ri)  
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightZero A) → ((ClRightZeroTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri eCl = (e Ri)  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightZero A) → ((Vec A n) → ((OpRightZeroTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars eOL = (e Ri)  
  evalOpB Ri vars (opOL x1 x2) = ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightZero A) → ((Vec A n) → ((OpRightZeroTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars eOL2 = (e Ri)  
  evalOp Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightZeroTerm → Set)} →  ((P eL) → (( (x1 x2 : RightZeroTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : RightZeroTerm) → (P x)))) 
  inductionB pel popl eL = pel  
  inductionB pel popl (opL x1 x2) = (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  inductionCl :  {A : Set} {P : ((ClRightZeroTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClRightZeroTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClRightZeroTerm A)) → (P x))))) 
  inductionCl psing pecl popcl (sing x1) = (psing x1)  
  inductionCl psing pecl popcl eCl = pecl  
  inductionCl psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightZeroTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpRightZeroTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpRightZeroTerm n)) → (P x))))) 
  inductionOpB pv peol popol (v x1) = (pv x1)  
  inductionOpB pv peol popol eOL = peol  
  inductionOpB pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightZeroTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpRightZeroTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpRightZeroTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  stageB :  (RightZeroTerm → (Staged RightZeroTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightZeroTerm A) → (Staged (ClRightZeroTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl eCl = (Now eCl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightZeroTerm n) → (Staged (OpRightZeroTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB eOL = (Now eOL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightZeroTerm2 n A) → (Staged (OpRightZeroTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 