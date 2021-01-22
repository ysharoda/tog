
module UnaryOperation   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsUnaryOperation  (A : Set) (prim : (A → A)) : Set where 
    
  record UnaryOperation  (A : Set) : Set where 
     field  
      prim : (A → A) 
      isUnaryOperation : (IsUnaryOperation A prim)  
  
  open UnaryOperation
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A))  
  
  record Hom  {A1 : Set} {A2 : Set} (Un1 : (UnaryOperation A1)) (Un2 : (UnaryOperation A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim Un1) x1)) ≡ ((prim Un2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Un1 : (UnaryOperation A1)) (Un2 : (UnaryOperation A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Un1) x1) ((prim Un2) y1))))  
  
  data UnaryOperationTerm   : Set where 
      primL : (UnaryOperationTerm → UnaryOperationTerm)  
      
  data ClUnaryOperationTerm  (A : Set) : Set where 
      sing : (A → (ClUnaryOperationTerm A)) 
      primCl : ((ClUnaryOperationTerm A) → (ClUnaryOperationTerm A))  
      
  data OpUnaryOperationTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpUnaryOperationTerm n)) 
      primOL : ((OpUnaryOperationTerm n) → (OpUnaryOperationTerm n))  
      
  data OpUnaryOperationTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpUnaryOperationTerm2 n A)) 
      sing2 : (A → (OpUnaryOperationTerm2 n A)) 
      primOL2 : ((OpUnaryOperationTerm2 n A) → (OpUnaryOperationTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClUnaryOperationTerm A) → (ClUnaryOperationTerm A)) 
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpUnaryOperationTerm n) → (OpUnaryOperationTerm n)) 
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpUnaryOperationTerm2 n A) → (OpUnaryOperationTerm2 n A)) 
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((UnaryOperation A) → (UnaryOperationTerm → A)) 
  evalB Un (primL x1) = ((prim Un) (evalB Un x1))  
  evalCl :  {A : Set} →  ((UnaryOperation A) → ((ClUnaryOperationTerm A) → A)) 
  evalCl Un (sing x1) = x1  
  evalCl Un (primCl x1) = ((prim Un) (evalCl Un x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((UnaryOperation A) → ((Vec A n) → ((OpUnaryOperationTerm n) → A))) 
  evalOpB Un vars (v x1) = (lookup vars x1)  
  evalOpB Un vars (primOL x1) = ((prim Un) (evalOpB Un vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((UnaryOperation A) → ((Vec A n) → ((OpUnaryOperationTerm2 n A) → A))) 
  evalOp Un vars (v2 x1) = (lookup vars x1)  
  evalOp Un vars (sing2 x1) = x1  
  evalOp Un vars (primOL2 x1) = ((prim Un) (evalOp Un vars x1))  
  inductionB :  {P : (UnaryOperationTerm → Set)} →  (( (x1 : UnaryOperationTerm) → ((P x1) → (P (primL x1)))) → ( (x : UnaryOperationTerm) → (P x))) 
  inductionB ppriml (primL x1) = (ppriml _ (inductionB ppriml x1))  
  inductionCl :  {A : Set} {P : ((ClUnaryOperationTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClUnaryOperationTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClUnaryOperationTerm A)) → (P x)))) 
  inductionCl psing pprimcl (sing x1) = (psing x1)  
  inductionCl psing pprimcl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpUnaryOperationTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpUnaryOperationTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpUnaryOperationTerm n)) → (P x)))) 
  inductionOpB pv pprimol (v x1) = (pv x1)  
  inductionOpB pv pprimol (primOL x1) = (pprimol _ (inductionOpB pv pprimol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpUnaryOperationTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpUnaryOperationTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpUnaryOperationTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 x1))  
  stageB :  (UnaryOperationTerm → (Staged UnaryOperationTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClUnaryOperationTerm A) → (Staged (ClUnaryOperationTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpUnaryOperationTerm n) → (Staged (OpUnaryOperationTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpUnaryOperationTerm2 n A) → (Staged (OpUnaryOperationTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A))  
  
 