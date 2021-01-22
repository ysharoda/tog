
module RightCancellativeSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightCancellativeSemigroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      rightCancellative : ( {x y z : A} → ((op x z) ≡ (op y z) → x ≡ y))  
  
  open RightCancellativeSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      rightCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP xP zP) ≡ (opP yP zP) → xP ≡ yP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightCancellativeSemigroup A1)) (Ri2 : (RightCancellativeSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightCancellativeSemigroup A1)) (Ri2 : (RightCancellativeSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))  
  
  data RightCancellativeSemigroupTerm   : Set where 
      opL : (RightCancellativeSemigroupTerm → (RightCancellativeSemigroupTerm → RightCancellativeSemigroupTerm))  
      
  data ClRightCancellativeSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClRightCancellativeSemigroupTerm A)) 
      opCl : ((ClRightCancellativeSemigroupTerm A) → ((ClRightCancellativeSemigroupTerm A) → (ClRightCancellativeSemigroupTerm A)))  
      
  data OpRightCancellativeSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightCancellativeSemigroupTerm n)) 
      opOL : ((OpRightCancellativeSemigroupTerm n) → ((OpRightCancellativeSemigroupTerm n) → (OpRightCancellativeSemigroupTerm n)))  
      
  data OpRightCancellativeSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightCancellativeSemigroupTerm2 n A)) 
      sing2 : (A → (OpRightCancellativeSemigroupTerm2 n A)) 
      opOL2 : ((OpRightCancellativeSemigroupTerm2 n A) → ((OpRightCancellativeSemigroupTerm2 n A) → (OpRightCancellativeSemigroupTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightCancellativeSemigroupTerm A) → (ClRightCancellativeSemigroupTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightCancellativeSemigroupTerm n) → (OpRightCancellativeSemigroupTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightCancellativeSemigroupTerm2 n A) → (OpRightCancellativeSemigroupTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightCancellativeSemigroup A) → (RightCancellativeSemigroupTerm → A)) 
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightCancellativeSemigroup A) → ((ClRightCancellativeSemigroupTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightCancellativeSemigroup A) → ((Vec A n) → ((OpRightCancellativeSemigroupTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (opOL x1 x2) = ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightCancellativeSemigroup A) → ((Vec A n) → ((OpRightCancellativeSemigroupTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightCancellativeSemigroupTerm → Set)} →  (( (x1 x2 : RightCancellativeSemigroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : RightCancellativeSemigroupTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClRightCancellativeSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightCancellativeSemigroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClRightCancellativeSemigroupTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightCancellativeSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightCancellativeSemigroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpRightCancellativeSemigroupTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightCancellativeSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightCancellativeSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpRightCancellativeSemigroupTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (RightCancellativeSemigroupTerm → (Staged RightCancellativeSemigroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightCancellativeSemigroupTerm A) → (Staged (ClRightCancellativeSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightCancellativeSemigroupTerm n) → (Staged (OpRightCancellativeSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightCancellativeSemigroupTerm2 n A) → (Staged (OpRightCancellativeSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 