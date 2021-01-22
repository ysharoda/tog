
module UnaryDistributes   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsUnaryDistributes  (A : Set) (prim : (A → A)) (op : (A → (A → A))) : Set where 
     field  
      distribute_prim_op : ( {x y : A} → (prim (op x y)) ≡ (op (prim x) (prim y)))  
  
  record UnaryDistributes  (A : Set) : Set where 
     field  
      prim : (A → A) 
      op : (A → (A → A)) 
      isUnaryDistributes : (IsUnaryDistributes A prim op)  
  
  open UnaryDistributes
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      distribute_prim_opP : ( {xP yP : (Prod A A)} → (primP (opP xP yP)) ≡ (opP (primP xP) (primP yP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Un1 : (UnaryDistributes A1)) (Un2 : (UnaryDistributes A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim Un1) x1)) ≡ ((prim Un2) (hom x1))) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Un1) x1 x2)) ≡ ((op Un2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Un1 : (UnaryDistributes A1)) (Un2 : (UnaryDistributes A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Un1) x1) ((prim Un2) y1)))) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Un1) x1 x2) ((op Un2) y1 y2)))))  
  
  data UnaryDistributesTerm   : Set where 
      primL : (UnaryDistributesTerm → UnaryDistributesTerm) 
      opL : (UnaryDistributesTerm → (UnaryDistributesTerm → UnaryDistributesTerm))  
      
  data ClUnaryDistributesTerm  (A : Set) : Set where 
      sing : (A → (ClUnaryDistributesTerm A)) 
      primCl : ((ClUnaryDistributesTerm A) → (ClUnaryDistributesTerm A)) 
      opCl : ((ClUnaryDistributesTerm A) → ((ClUnaryDistributesTerm A) → (ClUnaryDistributesTerm A)))  
      
  data OpUnaryDistributesTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpUnaryDistributesTerm n)) 
      primOL : ((OpUnaryDistributesTerm n) → (OpUnaryDistributesTerm n)) 
      opOL : ((OpUnaryDistributesTerm n) → ((OpUnaryDistributesTerm n) → (OpUnaryDistributesTerm n)))  
      
  data OpUnaryDistributesTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpUnaryDistributesTerm2 n A)) 
      sing2 : (A → (OpUnaryDistributesTerm2 n A)) 
      primOL2 : ((OpUnaryDistributesTerm2 n A) → (OpUnaryDistributesTerm2 n A)) 
      opOL2 : ((OpUnaryDistributesTerm2 n A) → ((OpUnaryDistributesTerm2 n A) → (OpUnaryDistributesTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClUnaryDistributesTerm A) → (ClUnaryDistributesTerm A)) 
  simplifyCl (opCl (primCl x) (primCl y)) = (primCl (opCl x y))  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpUnaryDistributesTerm n) → (OpUnaryDistributesTerm n)) 
  simplifyOpB (opOL (primOL x) (primOL y)) = (primOL (opOL x y))  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpUnaryDistributesTerm2 n A) → (OpUnaryDistributesTerm2 n A)) 
  simplifyOp (opOL2 (primOL2 x) (primOL2 y)) = (primOL2 (opOL2 x y))  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((UnaryDistributes A) → (UnaryDistributesTerm → A)) 
  evalB Un (primL x1) = ((prim Un) (evalB Un x1))  
  evalB Un (opL x1 x2) = ((op Un) (evalB Un x1) (evalB Un x2))  
  evalCl :  {A : Set} →  ((UnaryDistributes A) → ((ClUnaryDistributesTerm A) → A)) 
  evalCl Un (sing x1) = x1  
  evalCl Un (primCl x1) = ((prim Un) (evalCl Un x1))  
  evalCl Un (opCl x1 x2) = ((op Un) (evalCl Un x1) (evalCl Un x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((UnaryDistributes A) → ((Vec A n) → ((OpUnaryDistributesTerm n) → A))) 
  evalOpB Un vars (v x1) = (lookup vars x1)  
  evalOpB Un vars (primOL x1) = ((prim Un) (evalOpB Un vars x1))  
  evalOpB Un vars (opOL x1 x2) = ((op Un) (evalOpB Un vars x1) (evalOpB Un vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((UnaryDistributes A) → ((Vec A n) → ((OpUnaryDistributesTerm2 n A) → A))) 
  evalOp Un vars (v2 x1) = (lookup vars x1)  
  evalOp Un vars (sing2 x1) = x1  
  evalOp Un vars (primOL2 x1) = ((prim Un) (evalOp Un vars x1))  
  evalOp Un vars (opOL2 x1 x2) = ((op Un) (evalOp Un vars x1) (evalOp Un vars x2))  
  inductionB :  {P : (UnaryDistributesTerm → Set)} →  (( (x1 : UnaryDistributesTerm) → ((P x1) → (P (primL x1)))) → (( (x1 x2 : UnaryDistributesTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : UnaryDistributesTerm) → (P x)))) 
  inductionB ppriml popl (primL x1) = (ppriml _ (inductionB ppriml popl x1))  
  inductionB ppriml popl (opL x1 x2) = (popl _ _ (inductionB ppriml popl x1) (inductionB ppriml popl x2))  
  inductionCl :  {A : Set} {P : ((ClUnaryDistributesTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClUnaryDistributesTerm A)) → ((P x1) → (P (primCl x1)))) → (( (x1 x2 : (ClUnaryDistributesTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClUnaryDistributesTerm A)) → (P x))))) 
  inductionCl psing pprimcl popcl (sing x1) = (psing x1)  
  inductionCl psing pprimcl popcl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl popcl x1))  
  inductionCl psing pprimcl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pprimcl popcl x1) (inductionCl psing pprimcl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpUnaryDistributesTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpUnaryDistributesTerm n)) → ((P x1) → (P (primOL x1)))) → (( (x1 x2 : (OpUnaryDistributesTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpUnaryDistributesTerm n)) → (P x))))) 
  inductionOpB pv pprimol popol (v x1) = (pv x1)  
  inductionOpB pv pprimol popol (primOL x1) = (pprimol _ (inductionOpB pv pprimol popol x1))  
  inductionOpB pv pprimol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv pprimol popol x1) (inductionOpB pv pprimol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpUnaryDistributesTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpUnaryDistributesTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → (( (x1 x2 : (OpUnaryDistributesTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpUnaryDistributesTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 pprimol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 popol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 popol2 x1))  
  inductionOp pv2 psing2 pprimol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 pprimol2 popol2 x1) (inductionOp pv2 psing2 pprimol2 popol2 x2))  
  stageB :  (UnaryDistributesTerm → (Staged UnaryDistributesTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClUnaryDistributesTerm A) → (Staged (ClUnaryDistributesTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpUnaryDistributesTerm n) → (Staged (OpUnaryDistributesTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpUnaryDistributesTerm2 n A) → (Staged (OpUnaryDistributesTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 