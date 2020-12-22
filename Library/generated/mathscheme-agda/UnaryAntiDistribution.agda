
module UnaryAntiDistribution   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record UnaryAntiDistribution  (A : Set) : Set where 
     field  
      prim : (A → A) 
      op : (A → (A → A)) 
      antidis_prim_op : ( {x y : A} → (prim (op x y)) ≡ (op (prim y) (prim x)))  
  
  open UnaryAntiDistribution
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      antidis_prim_opP : ( {xP yP : (Prod A A)} → (primP (opP xP yP)) ≡ (opP (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Un1 : (UnaryAntiDistribution A1)) (Un2 : (UnaryAntiDistribution A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim Un1) x1)) ≡ ((prim Un2) (hom x1))) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Un1) x1 x2)) ≡ ((op Un2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Un1 : (UnaryAntiDistribution A1)) (Un2 : (UnaryAntiDistribution A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Un1) x1) ((prim Un2) y1)))) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Un1) x1 x2) ((op Un2) y1 y2)))))  
  
  data UnaryAntiDistributionTerm   : Set where 
      primL : (UnaryAntiDistributionTerm → UnaryAntiDistributionTerm) 
      opL : (UnaryAntiDistributionTerm → (UnaryAntiDistributionTerm → UnaryAntiDistributionTerm))  
      
  data ClUnaryAntiDistributionTerm  (A : Set) : Set where 
      sing : (A → (ClUnaryAntiDistributionTerm A)) 
      primCl : ((ClUnaryAntiDistributionTerm A) → (ClUnaryAntiDistributionTerm A)) 
      opCl : ((ClUnaryAntiDistributionTerm A) → ((ClUnaryAntiDistributionTerm A) → (ClUnaryAntiDistributionTerm A)))  
      
  data OpUnaryAntiDistributionTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpUnaryAntiDistributionTerm n)) 
      primOL : ((OpUnaryAntiDistributionTerm n) → (OpUnaryAntiDistributionTerm n)) 
      opOL : ((OpUnaryAntiDistributionTerm n) → ((OpUnaryAntiDistributionTerm n) → (OpUnaryAntiDistributionTerm n)))  
      
  data OpUnaryAntiDistributionTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpUnaryAntiDistributionTerm2 n A)) 
      sing2 : (A → (OpUnaryAntiDistributionTerm2 n A)) 
      primOL2 : ((OpUnaryAntiDistributionTerm2 n A) → (OpUnaryAntiDistributionTerm2 n A)) 
      opOL2 : ((OpUnaryAntiDistributionTerm2 n A) → ((OpUnaryAntiDistributionTerm2 n A) → (OpUnaryAntiDistributionTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClUnaryAntiDistributionTerm A) → (ClUnaryAntiDistributionTerm A)) 
  simplifyCl _ (opCl (primCl y) (primCl x)) = (primCl (opCl x y))  
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpUnaryAntiDistributionTerm n) → (OpUnaryAntiDistributionTerm n)) 
  simplifyOpB _ (opOL (primOL y) (primOL x)) = (primOL (opOL x y))  
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpUnaryAntiDistributionTerm2 n A) → (OpUnaryAntiDistributionTerm2 n A)) 
  simplifyOp _ _ (opOL2 (primOL2 y) (primOL2 x)) = (primOL2 (opOL2 x y))  
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((UnaryAntiDistribution A) → (UnaryAntiDistributionTerm → A)) 
  evalB Un (primL x1) = ((prim Un) (evalB Un x1))  
  evalB Un (opL x1 x2) = ((op Un) (evalB Un x1) (evalB Un x2))  
  evalCl :  {A : Set} →  ((UnaryAntiDistribution A) → ((ClUnaryAntiDistributionTerm A) → A)) 
  evalCl Un (sing x1) = x1  
  evalCl Un (primCl x1) = ((prim Un) (evalCl Un x1))  
  evalCl Un (opCl x1 x2) = ((op Un) (evalCl Un x1) (evalCl Un x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((UnaryAntiDistribution A) → ((Vec A n) → ((OpUnaryAntiDistributionTerm n) → A))) 
  evalOpB n Un vars (v x1) = (lookup vars x1)  
  evalOpB n Un vars (primOL x1) = ((prim Un) (evalOpB n Un vars x1))  
  evalOpB n Un vars (opOL x1 x2) = ((op Un) (evalOpB n Un vars x1) (evalOpB n Un vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((UnaryAntiDistribution A) → ((Vec A n) → ((OpUnaryAntiDistributionTerm2 n A) → A))) 
  evalOp n Un vars (v2 x1) = (lookup vars x1)  
  evalOp n Un vars (sing2 x1) = x1  
  evalOp n Un vars (primOL2 x1) = ((prim Un) (evalOp n Un vars x1))  
  evalOp n Un vars (opOL2 x1 x2) = ((op Un) (evalOp n Un vars x1) (evalOp n Un vars x2))  
  inductionB :  (P : (UnaryAntiDistributionTerm → Set)) →  (( (x1 : UnaryAntiDistributionTerm) → ((P x1) → (P (primL x1)))) → (( (x1 x2 : UnaryAntiDistributionTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : UnaryAntiDistributionTerm) → (P x)))) 
  inductionB p ppriml popl (primL x1) = (ppriml _ (inductionB p ppriml popl x1))  
  inductionB p ppriml popl (opL x1 x2) = (popl _ _ (inductionB p ppriml popl x1) (inductionB p ppriml popl x2))  
  inductionCl :  (A : Set) (P : ((ClUnaryAntiDistributionTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClUnaryAntiDistributionTerm A)) → ((P x1) → (P (primCl x1)))) → (( (x1 x2 : (ClUnaryAntiDistributionTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClUnaryAntiDistributionTerm A)) → (P x))))) 
  inductionCl _ p psing pprimcl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pprimcl popcl (primCl x1) = (pprimcl _ (inductionCl _ p psing pprimcl popcl x1))  
  inductionCl _ p psing pprimcl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pprimcl popcl x1) (inductionCl _ p psing pprimcl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpUnaryAntiDistributionTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpUnaryAntiDistributionTerm n)) → ((P x1) → (P (primOL x1)))) → (( (x1 x2 : (OpUnaryAntiDistributionTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpUnaryAntiDistributionTerm n)) → (P x))))) 
  inductionOpB _ p pv pprimol popol (v x1) = (pv x1)  
  inductionOpB _ p pv pprimol popol (primOL x1) = (pprimol _ (inductionOpB _ p pv pprimol popol x1))  
  inductionOpB _ p pv pprimol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv pprimol popol x1) (inductionOpB _ p pv pprimol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpUnaryAntiDistributionTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpUnaryAntiDistributionTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → (( (x1 x2 : (OpUnaryAntiDistributionTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpUnaryAntiDistributionTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 pprimol2 popol2 x1))  
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 pprimol2 popol2 x1) (inductionOp _ _ p pv2 psing2 pprimol2 popol2 x2))  
  stageB :  (UnaryAntiDistributionTerm → (Staged UnaryAntiDistributionTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClUnaryAntiDistributionTerm A) → (Staged (ClUnaryAntiDistributionTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpUnaryAntiDistributionTerm n) → (Staged (OpUnaryAntiDistributionTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpUnaryAntiDistributionTerm2 n A) → (Staged (OpUnaryAntiDistributionTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 