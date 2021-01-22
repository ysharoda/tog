
module RightUnital   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightUnital  (A : Set) (e : A) (op : (A → (A → A))) : Set where 
     field  
      runit_e : ( {x : A} → (op x e) ≡ x)  
  
  record RightUnital  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      isRightUnital : (IsRightUnital A e op)  
  
  open RightUnital
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightUnital A1)) (Ri2 : (RightUnital A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Ri1)) ≡ (e Ri2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightUnital A1)) (Ri2 : (RightUnital A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Ri1) (e Ri2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))  
  
  data RightUnitalTerm   : Set where 
      eL : RightUnitalTerm 
      opL : (RightUnitalTerm → (RightUnitalTerm → RightUnitalTerm))  
      
  data ClRightUnitalTerm  (A : Set) : Set where 
      sing : (A → (ClRightUnitalTerm A)) 
      eCl : (ClRightUnitalTerm A) 
      opCl : ((ClRightUnitalTerm A) → ((ClRightUnitalTerm A) → (ClRightUnitalTerm A)))  
      
  data OpRightUnitalTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightUnitalTerm n)) 
      eOL : (OpRightUnitalTerm n) 
      opOL : ((OpRightUnitalTerm n) → ((OpRightUnitalTerm n) → (OpRightUnitalTerm n)))  
      
  data OpRightUnitalTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightUnitalTerm2 n A)) 
      sing2 : (A → (OpRightUnitalTerm2 n A)) 
      eOL2 : (OpRightUnitalTerm2 n A) 
      opOL2 : ((OpRightUnitalTerm2 n A) → ((OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightUnitalTerm A) → (ClRightUnitalTerm A)) 
  simplifyCl (opCl x eCl) = x  
  simplifyCl eCl = eCl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightUnitalTerm n) → (OpRightUnitalTerm n)) 
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB eOL = eOL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A)) 
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp eOL2 = eOL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightUnital A) → (RightUnitalTerm → A)) 
  evalB Ri eL = (e Ri)  
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightUnital A) → ((ClRightUnitalTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri eCl = (e Ri)  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightUnital A) → ((Vec A n) → ((OpRightUnitalTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars eOL = (e Ri)  
  evalOpB Ri vars (opOL x1 x2) = ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightUnital A) → ((Vec A n) → ((OpRightUnitalTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars eOL2 = (e Ri)  
  evalOp Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightUnitalTerm → Set)} →  ((P eL) → (( (x1 x2 : RightUnitalTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : RightUnitalTerm) → (P x)))) 
  inductionB pel popl eL = pel  
  inductionB pel popl (opL x1 x2) = (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  inductionCl :  {A : Set} {P : ((ClRightUnitalTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClRightUnitalTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClRightUnitalTerm A)) → (P x))))) 
  inductionCl psing pecl popcl (sing x1) = (psing x1)  
  inductionCl psing pecl popcl eCl = pecl  
  inductionCl psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightUnitalTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpRightUnitalTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpRightUnitalTerm n)) → (P x))))) 
  inductionOpB pv peol popol (v x1) = (pv x1)  
  inductionOpB pv peol popol eOL = peol  
  inductionOpB pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightUnitalTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpRightUnitalTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpRightUnitalTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  stageB :  (RightUnitalTerm → (Staged RightUnitalTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightUnitalTerm A) → (Staged (ClRightUnitalTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl eCl = (Now eCl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightUnitalTerm n) → (Staged (OpRightUnitalTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB eOL = (Now eOL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightUnitalTerm2 n A) → (Staged (OpRightUnitalTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 