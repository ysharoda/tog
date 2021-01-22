
module RightMonoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightMonoid  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z)))  
  
  open RightMonoid
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightMonoid A1)) (Ri2 : (RightMonoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2))) 
      pres-e : (hom (e Ri1)) ≡ (e Ri2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightMonoid A1)) (Ri2 : (RightMonoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2))))) 
      interp-e : (interp (e Ri1) (e Ri2))  
  
  data RightMonoidTerm   : Set where 
      opL : (RightMonoidTerm → (RightMonoidTerm → RightMonoidTerm)) 
      eL : RightMonoidTerm  
      
  data ClRightMonoidTerm  (A : Set) : Set where 
      sing : (A → (ClRightMonoidTerm A)) 
      opCl : ((ClRightMonoidTerm A) → ((ClRightMonoidTerm A) → (ClRightMonoidTerm A))) 
      eCl : (ClRightMonoidTerm A)  
      
  data OpRightMonoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightMonoidTerm n)) 
      opOL : ((OpRightMonoidTerm n) → ((OpRightMonoidTerm n) → (OpRightMonoidTerm n))) 
      eOL : (OpRightMonoidTerm n)  
      
  data OpRightMonoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightMonoidTerm2 n A)) 
      sing2 : (A → (OpRightMonoidTerm2 n A)) 
      opOL2 : ((OpRightMonoidTerm2 n A) → ((OpRightMonoidTerm2 n A) → (OpRightMonoidTerm2 n A))) 
      eOL2 : (OpRightMonoidTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClRightMonoidTerm A) → (ClRightMonoidTerm A)) 
  simplifyCl (opCl x eCl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightMonoidTerm n) → (OpRightMonoidTerm n)) 
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightMonoidTerm2 n A) → (OpRightMonoidTerm2 n A)) 
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightMonoid A) → (RightMonoidTerm → A)) 
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri eL = (e Ri)  
  evalCl :  {A : Set} →  ((RightMonoid A) → ((ClRightMonoidTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri eCl = (e Ri)  
  evalOpB :  {A : Set} {n : Nat} →  ((RightMonoid A) → ((Vec A n) → ((OpRightMonoidTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (opOL x1 x2) = ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars eOL = (e Ri)  
  evalOp :  {A : Set} {n : Nat} →  ((RightMonoid A) → ((Vec A n) → ((OpRightMonoidTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars eOL2 = (e Ri)  
  inductionB :  {P : (RightMonoidTerm → Set)} →  (( (x1 x2 : RightMonoidTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : RightMonoidTerm) → (P x)))) 
  inductionB popl pel (opL x1 x2) = (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  inductionB popl pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClRightMonoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightMonoidTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClRightMonoidTerm A)) → (P x))))) 
  inductionCl psing popcl pecl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  inductionCl psing popcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpRightMonoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightMonoidTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpRightMonoidTerm n)) → (P x))))) 
  inductionOpB pv popol peol (v x1) = (pv x1)  
  inductionOpB pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  inductionOpB pv popol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightMonoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpRightMonoidTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (RightMonoidTerm → (Staged RightMonoidTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClRightMonoidTerm A) → (Staged (ClRightMonoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpRightMonoidTerm n) → (Staged (OpRightMonoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightMonoidTerm2 n A) → (Staged (OpRightMonoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 