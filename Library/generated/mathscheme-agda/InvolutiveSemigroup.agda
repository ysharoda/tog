
module InvolutiveSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveSemigroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      prim : (A → A) 
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x) 
      antidis_prim_op : ( {x y : A} → (prim (op x y)) ≡ (op (prim y) (prim x)))  
  
  open InvolutiveSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      primP : ((Prod A A) → (Prod A A)) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      involutive_primP : ( {xP : (Prod A A)} → (primP (primP xP)) ≡ xP) 
      antidis_prim_opP : ( {xP yP : (Prod A A)} → (primP (opP xP yP)) ≡ (opP (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveSemigroup A1)) (In2 : (InvolutiveSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op In1) x1 x2)) ≡ ((op In2) (hom x1) (hom x2))) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveSemigroup A1)) (In2 : (InvolutiveSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2))))) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))  
  
  data InvolutiveSemigroupTerm   : Set where 
      opL : (InvolutiveSemigroupTerm → (InvolutiveSemigroupTerm → InvolutiveSemigroupTerm)) 
      primL : (InvolutiveSemigroupTerm → InvolutiveSemigroupTerm)  
      
  data ClInvolutiveSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveSemigroupTerm A)) 
      opCl : ((ClInvolutiveSemigroupTerm A) → ((ClInvolutiveSemigroupTerm A) → (ClInvolutiveSemigroupTerm A))) 
      primCl : ((ClInvolutiveSemigroupTerm A) → (ClInvolutiveSemigroupTerm A))  
      
  data OpInvolutiveSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveSemigroupTerm n)) 
      opOL : ((OpInvolutiveSemigroupTerm n) → ((OpInvolutiveSemigroupTerm n) → (OpInvolutiveSemigroupTerm n))) 
      primOL : ((OpInvolutiveSemigroupTerm n) → (OpInvolutiveSemigroupTerm n))  
      
  data OpInvolutiveSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveSemigroupTerm2 n A)) 
      sing2 : (A → (OpInvolutiveSemigroupTerm2 n A)) 
      opOL2 : ((OpInvolutiveSemigroupTerm2 n A) → ((OpInvolutiveSemigroupTerm2 n A) → (OpInvolutiveSemigroupTerm2 n A))) 
      primOL2 : ((OpInvolutiveSemigroupTerm2 n A) → (OpInvolutiveSemigroupTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveSemigroupTerm A) → (ClInvolutiveSemigroupTerm A)) 
  simplifyCl (primCl (primCl x)) = x  
  simplifyCl (opCl (primCl y) (primCl x)) = (primCl (opCl x y))  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveSemigroupTerm n) → (OpInvolutiveSemigroupTerm n)) 
  simplifyOpB (primOL (primOL x)) = x  
  simplifyOpB (opOL (primOL y) (primOL x)) = (primOL (opOL x y))  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveSemigroupTerm2 n A) → (OpInvolutiveSemigroupTerm2 n A)) 
  simplifyOp (primOL2 (primOL2 x)) = x  
  simplifyOp (opOL2 (primOL2 y) (primOL2 x)) = (primOL2 (opOL2 x y))  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveSemigroup A) → (InvolutiveSemigroupTerm → A)) 
  evalB In (opL x1 x2) = ((op In) (evalB In x1) (evalB In x2))  
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InvolutiveSemigroup A) → ((ClInvolutiveSemigroupTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (opCl x1 x2) = ((op In) (evalCl In x1) (evalCl In x2))  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveSemigroup A) → ((Vec A n) → ((OpInvolutiveSemigroupTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (opOL x1 x2) = ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveSemigroup A) → ((Vec A n) → ((OpInvolutiveSemigroupTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (opOL2 x1 x2) = ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  inductionB :  {P : (InvolutiveSemigroupTerm → Set)} →  (( (x1 x2 : InvolutiveSemigroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 : InvolutiveSemigroupTerm) → ((P x1) → (P (primL x1)))) → ( (x : InvolutiveSemigroupTerm) → (P x)))) 
  inductionB popl ppriml (opL x1 x2) = (popl _ _ (inductionB popl ppriml x1) (inductionB popl ppriml x2))  
  inductionB popl ppriml (primL x1) = (ppriml _ (inductionB popl ppriml x1))  
  inductionCl :  {A : Set} {P : ((ClInvolutiveSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClInvolutiveSemigroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 : (ClInvolutiveSemigroupTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClInvolutiveSemigroupTerm A)) → (P x))))) 
  inductionCl psing popcl pprimcl (sing x1) = (psing x1)  
  inductionCl psing popcl pprimcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pprimcl x1) (inductionCl psing popcl pprimcl x2))  
  inductionCl psing popcl pprimcl (primCl x1) = (pprimcl _ (inductionCl psing popcl pprimcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpInvolutiveSemigroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 : (OpInvolutiveSemigroupTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpInvolutiveSemigroupTerm n)) → (P x))))) 
  inductionOpB pv popol pprimol (v x1) = (pv x1)  
  inductionOpB pv popol pprimol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol pprimol x1) (inductionOpB pv popol pprimol x2))  
  inductionOpB pv popol pprimol (primOL x1) = (pprimol _ (inductionOpB pv popol pprimol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpInvolutiveSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 : (OpInvolutiveSemigroupTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpInvolutiveSemigroupTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 pprimol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 pprimol2 x1) (inductionOp pv2 psing2 popol2 pprimol2 x2))  
  inductionOp pv2 psing2 popol2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 popol2 pprimol2 x1))  
  stageB :  (InvolutiveSemigroupTerm → (Staged InvolutiveSemigroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClInvolutiveSemigroupTerm A) → (Staged (ClInvolutiveSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpInvolutiveSemigroupTerm n) → (Staged (OpInvolutiveSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveSemigroupTerm2 n A) → (Staged (OpInvolutiveSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      primT : ((Repr A) → (Repr A))  
  
 