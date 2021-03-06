
module PointedSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointedSemigroup  (A : Set) (op : (A → (A → A))) (e : A) : Set where 
     field  
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z)))  
  
  record PointedSemigroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      isPointedSemigroup : (IsPointedSemigroup A op e)  
  
  open PointedSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedSemigroup A1)) (Po2 : (PointedSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Po1) x1 x2)) ≡ ((op Po2) (hom x1) (hom x2))) 
      pres-e : (hom (e Po1)) ≡ (e Po2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedSemigroup A1)) (Po2 : (PointedSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2))))) 
      interp-e : (interp (e Po1) (e Po2))  
  
  data PointedSemigroupTerm   : Set where 
      opL : (PointedSemigroupTerm → (PointedSemigroupTerm → PointedSemigroupTerm)) 
      eL : PointedSemigroupTerm  
      
  data ClPointedSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClPointedSemigroupTerm A)) 
      opCl : ((ClPointedSemigroupTerm A) → ((ClPointedSemigroupTerm A) → (ClPointedSemigroupTerm A))) 
      eCl : (ClPointedSemigroupTerm A)  
      
  data OpPointedSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedSemigroupTerm n)) 
      opOL : ((OpPointedSemigroupTerm n) → ((OpPointedSemigroupTerm n) → (OpPointedSemigroupTerm n))) 
      eOL : (OpPointedSemigroupTerm n)  
      
  data OpPointedSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedSemigroupTerm2 n A)) 
      sing2 : (A → (OpPointedSemigroupTerm2 n A)) 
      opOL2 : ((OpPointedSemigroupTerm2 n A) → ((OpPointedSemigroupTerm2 n A) → (OpPointedSemigroupTerm2 n A))) 
      eOL2 : (OpPointedSemigroupTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClPointedSemigroupTerm A) → (ClPointedSemigroupTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPointedSemigroupTerm n) → (OpPointedSemigroupTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPointedSemigroupTerm2 n A) → (OpPointedSemigroupTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedSemigroup A) → (PointedSemigroupTerm → A)) 
  evalB Po (opL x1 x2) = ((op Po) (evalB Po x1) (evalB Po x2))  
  evalB Po eL = (e Po)  
  evalCl :  {A : Set} →  ((PointedSemigroup A) → ((ClPointedSemigroupTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po (opCl x1 x2) = ((op Po) (evalCl Po x1) (evalCl Po x2))  
  evalCl Po eCl = (e Po)  
  evalOpB :  {A : Set} {n : Nat} →  ((PointedSemigroup A) → ((Vec A n) → ((OpPointedSemigroupTerm n) → A))) 
  evalOpB Po vars (v x1) = (lookup vars x1)  
  evalOpB Po vars (opOL x1 x2) = ((op Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  evalOpB Po vars eOL = (e Po)  
  evalOp :  {A : Set} {n : Nat} →  ((PointedSemigroup A) → ((Vec A n) → ((OpPointedSemigroupTerm2 n A) → A))) 
  evalOp Po vars (v2 x1) = (lookup vars x1)  
  evalOp Po vars (sing2 x1) = x1  
  evalOp Po vars (opOL2 x1 x2) = ((op Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  evalOp Po vars eOL2 = (e Po)  
  inductionB :  {P : (PointedSemigroupTerm → Set)} →  (( (x1 x2 : PointedSemigroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : PointedSemigroupTerm) → (P x)))) 
  inductionB popl pel (opL x1 x2) = (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  inductionB popl pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClPointedSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClPointedSemigroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClPointedSemigroupTerm A)) → (P x))))) 
  inductionCl psing popcl pecl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  inductionCl psing popcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpPointedSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpPointedSemigroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpPointedSemigroupTerm n)) → (P x))))) 
  inductionOpB pv popol peol (v x1) = (pv x1)  
  inductionOpB pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  inductionOpB pv popol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPointedSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpPointedSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpPointedSemigroupTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (PointedSemigroupTerm → (Staged PointedSemigroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClPointedSemigroupTerm A) → (Staged (ClPointedSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpPointedSemigroupTerm n) → (Staged (OpPointedSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpPointedSemigroupTerm2 n A) → (Staged (OpPointedSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 