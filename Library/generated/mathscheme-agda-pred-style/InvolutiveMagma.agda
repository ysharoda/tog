
module InvolutiveMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveMagma  (A : Set) (prim : (A → A)) (op : (A → (A → A))) : Set where 
     field  
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x) 
      antidis_prim_op : ( {x y : A} → (prim (op x y)) ≡ (op (prim y) (prim x)))  
  
  record InvolutiveMagma  (A : Set) : Set where 
     field  
      prim : (A → A) 
      op : (A → (A → A)) 
      isInvolutiveMagma : (IsInvolutiveMagma A prim op)  
  
  open InvolutiveMagma
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      involutive_primP : ( {xP : (Prod A A)} → (primP (primP xP)) ≡ xP) 
      antidis_prim_opP : ( {xP yP : (Prod A A)} → (primP (opP xP yP)) ≡ (opP (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveMagma A1)) (In2 : (InvolutiveMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1))) 
      pres-op : ( {x1 x2 : A1} → (hom ((op In1) x1 x2)) ≡ ((op In2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveMagma A1)) (In2 : (InvolutiveMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2)))))  
  
  data InvolutiveMagmaTerm   : Set where 
      primL : (InvolutiveMagmaTerm → InvolutiveMagmaTerm) 
      opL : (InvolutiveMagmaTerm → (InvolutiveMagmaTerm → InvolutiveMagmaTerm))  
      
  data ClInvolutiveMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveMagmaTerm A)) 
      primCl : ((ClInvolutiveMagmaTerm A) → (ClInvolutiveMagmaTerm A)) 
      opCl : ((ClInvolutiveMagmaTerm A) → ((ClInvolutiveMagmaTerm A) → (ClInvolutiveMagmaTerm A)))  
      
  data OpInvolutiveMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveMagmaTerm n)) 
      primOL : ((OpInvolutiveMagmaTerm n) → (OpInvolutiveMagmaTerm n)) 
      opOL : ((OpInvolutiveMagmaTerm n) → ((OpInvolutiveMagmaTerm n) → (OpInvolutiveMagmaTerm n)))  
      
  data OpInvolutiveMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveMagmaTerm2 n A)) 
      sing2 : (A → (OpInvolutiveMagmaTerm2 n A)) 
      primOL2 : ((OpInvolutiveMagmaTerm2 n A) → (OpInvolutiveMagmaTerm2 n A)) 
      opOL2 : ((OpInvolutiveMagmaTerm2 n A) → ((OpInvolutiveMagmaTerm2 n A) → (OpInvolutiveMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClInvolutiveMagmaTerm A) → (ClInvolutiveMagmaTerm A)) 
  simplifyCl _ (primCl (primCl x)) = x  
  simplifyCl _ (opCl (primCl y) (primCl x)) = (primCl (opCl x y))  
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpInvolutiveMagmaTerm n) → (OpInvolutiveMagmaTerm n)) 
  simplifyOpB _ (primOL (primOL x)) = x  
  simplifyOpB _ (opOL (primOL y) (primOL x)) = (primOL (opOL x y))  
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpInvolutiveMagmaTerm2 n A) → (OpInvolutiveMagmaTerm2 n A)) 
  simplifyOp _ _ (primOL2 (primOL2 x)) = x  
  simplifyOp _ _ (opOL2 (primOL2 y) (primOL2 x)) = (primOL2 (opOL2 x y))  
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveMagma A) → (InvolutiveMagmaTerm → A)) 
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalB In (opL x1 x2) = ((op In) (evalB In x1) (evalB In x2))  
  evalCl :  {A : Set} →  ((InvolutiveMagma A) → ((ClInvolutiveMagmaTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalCl In (opCl x1 x2) = ((op In) (evalCl In x1) (evalCl In x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((InvolutiveMagma A) → ((Vec A n) → ((OpInvolutiveMagmaTerm n) → A))) 
  evalOpB n In vars (v x1) = (lookup vars x1)  
  evalOpB n In vars (primOL x1) = ((prim In) (evalOpB n In vars x1))  
  evalOpB n In vars (opOL x1 x2) = ((op In) (evalOpB n In vars x1) (evalOpB n In vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((InvolutiveMagma A) → ((Vec A n) → ((OpInvolutiveMagmaTerm2 n A) → A))) 
  evalOp n In vars (v2 x1) = (lookup vars x1)  
  evalOp n In vars (sing2 x1) = x1  
  evalOp n In vars (primOL2 x1) = ((prim In) (evalOp n In vars x1))  
  evalOp n In vars (opOL2 x1 x2) = ((op In) (evalOp n In vars x1) (evalOp n In vars x2))  
  inductionB :  (P : (InvolutiveMagmaTerm → Set)) →  (( (x1 : InvolutiveMagmaTerm) → ((P x1) → (P (primL x1)))) → (( (x1 x2 : InvolutiveMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : InvolutiveMagmaTerm) → (P x)))) 
  inductionB p ppriml popl (primL x1) = (ppriml _ (inductionB p ppriml popl x1))  
  inductionB p ppriml popl (opL x1 x2) = (popl _ _ (inductionB p ppriml popl x1) (inductionB p ppriml popl x2))  
  inductionCl :  (A : Set) (P : ((ClInvolutiveMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInvolutiveMagmaTerm A)) → ((P x1) → (P (primCl x1)))) → (( (x1 x2 : (ClInvolutiveMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClInvolutiveMagmaTerm A)) → (P x))))) 
  inductionCl _ p psing pprimcl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pprimcl popcl (primCl x1) = (pprimcl _ (inductionCl _ p psing pprimcl popcl x1))  
  inductionCl _ p psing pprimcl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pprimcl popcl x1) (inductionCl _ p psing pprimcl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpInvolutiveMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInvolutiveMagmaTerm n)) → ((P x1) → (P (primOL x1)))) → (( (x1 x2 : (OpInvolutiveMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpInvolutiveMagmaTerm n)) → (P x))))) 
  inductionOpB _ p pv pprimol popol (v x1) = (pv x1)  
  inductionOpB _ p pv pprimol popol (primOL x1) = (pprimol _ (inductionOpB _ p pv pprimol popol x1))  
  inductionOpB _ p pv pprimol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv pprimol popol x1) (inductionOpB _ p pv pprimol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpInvolutiveMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInvolutiveMagmaTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → (( (x1 x2 : (OpInvolutiveMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpInvolutiveMagmaTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 pprimol2 popol2 x1))  
  inductionOp _ _ p pv2 psing2 pprimol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 pprimol2 popol2 x1) (inductionOp _ _ p pv2 psing2 pprimol2 popol2 x2))  
  stageB :  (InvolutiveMagmaTerm → (Staged InvolutiveMagmaTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClInvolutiveMagmaTerm A) → (Staged (ClInvolutiveMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpInvolutiveMagmaTerm n) → (Staged (OpInvolutiveMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpInvolutiveMagmaTerm2 n A) → (Staged (OpInvolutiveMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 