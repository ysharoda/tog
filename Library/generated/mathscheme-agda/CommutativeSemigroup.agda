
module CommutativeSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeSemigroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x)) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z)))  
  
  open CommutativeSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP)) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (CommutativeSemigroup A1)) (Co2 : (CommutativeSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Co1) x1 x2)) ≡ ((op Co2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (CommutativeSemigroup A1)) (Co2 : (CommutativeSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2)))))  
  
  data CommutativeSemigroupTerm   : Set where 
      opL : (CommutativeSemigroupTerm → (CommutativeSemigroupTerm → CommutativeSemigroupTerm))  
      
  data ClCommutativeSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClCommutativeSemigroupTerm A)) 
      opCl : ((ClCommutativeSemigroupTerm A) → ((ClCommutativeSemigroupTerm A) → (ClCommutativeSemigroupTerm A)))  
      
  data OpCommutativeSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCommutativeSemigroupTerm n)) 
      opOL : ((OpCommutativeSemigroupTerm n) → ((OpCommutativeSemigroupTerm n) → (OpCommutativeSemigroupTerm n)))  
      
  data OpCommutativeSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCommutativeSemigroupTerm2 n A)) 
      sing2 : (A → (OpCommutativeSemigroupTerm2 n A)) 
      opOL2 : ((OpCommutativeSemigroupTerm2 n A) → ((OpCommutativeSemigroupTerm2 n A) → (OpCommutativeSemigroupTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClCommutativeSemigroupTerm A) → (ClCommutativeSemigroupTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpCommutativeSemigroupTerm n) → (OpCommutativeSemigroupTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpCommutativeSemigroupTerm2 n A) → (OpCommutativeSemigroupTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativeSemigroup A) → (CommutativeSemigroupTerm → A)) 
  evalB Co (opL x1 x2) = ((op Co) (evalB Co x1) (evalB Co x2))  
  evalCl :  {A : Set} →  ((CommutativeSemigroup A) → ((ClCommutativeSemigroupTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (opCl x1 x2) = ((op Co) (evalCl Co x1) (evalCl Co x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((CommutativeSemigroup A) → ((Vec A n) → ((OpCommutativeSemigroupTerm n) → A))) 
  evalOpB Co vars (v x1) = (lookup vars x1)  
  evalOpB Co vars (opOL x1 x2) = ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((CommutativeSemigroup A) → ((Vec A n) → ((OpCommutativeSemigroupTerm2 n A) → A))) 
  evalOp Co vars (v2 x1) = (lookup vars x1)  
  evalOp Co vars (sing2 x1) = x1  
  evalOp Co vars (opOL2 x1 x2) = ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  inductionB :  {P : (CommutativeSemigroupTerm → Set)} →  (( (x1 x2 : CommutativeSemigroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : CommutativeSemigroupTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClCommutativeSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativeSemigroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClCommutativeSemigroupTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpCommutativeSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativeSemigroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpCommutativeSemigroupTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpCommutativeSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativeSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpCommutativeSemigroupTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (CommutativeSemigroupTerm → (Staged CommutativeSemigroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClCommutativeSemigroupTerm A) → (Staged (ClCommutativeSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpCommutativeSemigroupTerm n) → (Staged (OpCommutativeSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpCommutativeSemigroupTerm2 n A) → (Staged (OpCommutativeSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 