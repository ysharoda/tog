
module InvolutivePointedSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutivePointedSemigroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      prim : (A → A) 
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x) 
      antidis_prim_op : ( {x y : A} → (prim (op x y)) ≡ (op (prim y) (prim x)))  
  
  open InvolutivePointedSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS 
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      primP : ((Prod A A) → (Prod A A)) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      involutive_primP : ( {xP : (Prod A A)} → (primP (primP xP)) ≡ xP) 
      antidis_prim_opP : ( {xP yP : (Prod A A)} → (primP (opP xP yP)) ≡ (opP (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutivePointedSemigroup A1)) (In2 : (InvolutivePointedSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op In1) x1 x2)) ≡ ((op In2) (hom x1) (hom x2))) 
      pres-e : (hom (e In1)) ≡ (e In2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutivePointedSemigroup A1)) (In2 : (InvolutivePointedSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2))))) 
      interp-e : (interp (e In1) (e In2)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))  
  
  data InvolutivePointedSemigroupTerm   : Set where 
      opL : (InvolutivePointedSemigroupTerm → (InvolutivePointedSemigroupTerm → InvolutivePointedSemigroupTerm)) 
      eL : InvolutivePointedSemigroupTerm 
      primL : (InvolutivePointedSemigroupTerm → InvolutivePointedSemigroupTerm)  
      
  data ClInvolutivePointedSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutivePointedSemigroupTerm A)) 
      opCl : ((ClInvolutivePointedSemigroupTerm A) → ((ClInvolutivePointedSemigroupTerm A) → (ClInvolutivePointedSemigroupTerm A))) 
      eCl : (ClInvolutivePointedSemigroupTerm A) 
      primCl : ((ClInvolutivePointedSemigroupTerm A) → (ClInvolutivePointedSemigroupTerm A))  
      
  data OpInvolutivePointedSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutivePointedSemigroupTerm n)) 
      opOL : ((OpInvolutivePointedSemigroupTerm n) → ((OpInvolutivePointedSemigroupTerm n) → (OpInvolutivePointedSemigroupTerm n))) 
      eOL : (OpInvolutivePointedSemigroupTerm n) 
      primOL : ((OpInvolutivePointedSemigroupTerm n) → (OpInvolutivePointedSemigroupTerm n))  
      
  data OpInvolutivePointedSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutivePointedSemigroupTerm2 n A)) 
      sing2 : (A → (OpInvolutivePointedSemigroupTerm2 n A)) 
      opOL2 : ((OpInvolutivePointedSemigroupTerm2 n A) → ((OpInvolutivePointedSemigroupTerm2 n A) → (OpInvolutivePointedSemigroupTerm2 n A))) 
      eOL2 : (OpInvolutivePointedSemigroupTerm2 n A) 
      primOL2 : ((OpInvolutivePointedSemigroupTerm2 n A) → (OpInvolutivePointedSemigroupTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClInvolutivePointedSemigroupTerm A) → (ClInvolutivePointedSemigroupTerm A)) 
  simplifyCl _ (primCl (primCl x)) = x  
  simplifyCl _ (opCl (primCl y) (primCl x)) = (primCl (opCl x y))  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpInvolutivePointedSemigroupTerm n) → (OpInvolutivePointedSemigroupTerm n)) 
  simplifyOpB _ (primOL (primOL x)) = x  
  simplifyOpB _ (opOL (primOL y) (primOL x)) = (primOL (opOL x y))  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpInvolutivePointedSemigroupTerm2 n A) → (OpInvolutivePointedSemigroupTerm2 n A)) 
  simplifyOp _ _ (primOL2 (primOL2 x)) = x  
  simplifyOp _ _ (opOL2 (primOL2 y) (primOL2 x)) = (primOL2 (opOL2 x y))  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutivePointedSemigroup A) → (InvolutivePointedSemigroupTerm → A)) 
  evalB In (opL x1 x2) = ((op In) (evalB In x1) (evalB In x2))  
  evalB In eL = (e In)  
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InvolutivePointedSemigroup A) → ((ClInvolutivePointedSemigroupTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (opCl x1 x2) = ((op In) (evalCl In x1) (evalCl In x2))  
  evalCl In eCl = (e In)  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((InvolutivePointedSemigroup A) → ((Vec A n) → ((OpInvolutivePointedSemigroupTerm n) → A))) 
  evalOpB n In vars (v x1) = (lookup vars x1)  
  evalOpB n In vars (opOL x1 x2) = ((op In) (evalOpB n In vars x1) (evalOpB n In vars x2))  
  evalOpB n In vars eOL = (e In)  
  evalOpB n In vars (primOL x1) = ((prim In) (evalOpB n In vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((InvolutivePointedSemigroup A) → ((Vec A n) → ((OpInvolutivePointedSemigroupTerm2 n A) → A))) 
  evalOp n In vars (v2 x1) = (lookup vars x1)  
  evalOp n In vars (sing2 x1) = x1  
  evalOp n In vars (opOL2 x1 x2) = ((op In) (evalOp n In vars x1) (evalOp n In vars x2))  
  evalOp n In vars eOL2 = (e In)  
  evalOp n In vars (primOL2 x1) = ((prim In) (evalOp n In vars x1))  
  inductionB :  (P : (InvolutivePointedSemigroupTerm → Set)) →  (( (x1 x2 : InvolutivePointedSemigroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (( (x1 : InvolutivePointedSemigroupTerm) → ((P x1) → (P (primL x1)))) → ( (x : InvolutivePointedSemigroupTerm) → (P x))))) 
  inductionB p popl pel ppriml (opL x1 x2) = (popl _ _ (inductionB p popl pel ppriml x1) (inductionB p popl pel ppriml x2))  
  inductionB p popl pel ppriml eL = pel  
  inductionB p popl pel ppriml (primL x1) = (ppriml _ (inductionB p popl pel ppriml x1))  
  inductionCl :  (A : Set) (P : ((ClInvolutivePointedSemigroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClInvolutivePointedSemigroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (( (x1 : (ClInvolutivePointedSemigroupTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClInvolutivePointedSemigroupTerm A)) → (P x)))))) 
  inductionCl _ p psing popcl pecl pprimcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl pecl pprimcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl pecl pprimcl x1) (inductionCl _ p psing popcl pecl pprimcl x2))  
  inductionCl _ p psing popcl pecl pprimcl eCl = pecl  
  inductionCl _ p psing popcl pecl pprimcl (primCl x1) = (pprimcl _ (inductionCl _ p psing popcl pecl pprimcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpInvolutivePointedSemigroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpInvolutivePointedSemigroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (( (x1 : (OpInvolutivePointedSemigroupTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpInvolutivePointedSemigroupTerm n)) → (P x)))))) 
  inductionOpB _ p pv popol peol pprimol (v x1) = (pv x1)  
  inductionOpB _ p pv popol peol pprimol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol peol pprimol x1) (inductionOpB _ p pv popol peol pprimol x2))  
  inductionOpB _ p pv popol peol pprimol eOL = peol  
  inductionOpB _ p pv popol peol pprimol (primOL x1) = (pprimol _ (inductionOpB _ p pv popol peol pprimol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpInvolutivePointedSemigroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpInvolutivePointedSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (( (x1 : (OpInvolutivePointedSemigroupTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpInvolutivePointedSemigroupTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 x1) (inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 popol2 peol2 pprimol2 x1))  
  stageB :  (InvolutivePointedSemigroupTerm → (Staged InvolutivePointedSemigroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClInvolutivePointedSemigroupTerm A) → (Staged (ClInvolutivePointedSemigroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpInvolutivePointedSemigroupTerm n) → (Staged (OpInvolutivePointedSemigroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpInvolutivePointedSemigroupTerm2 n A) → (Staged (OpInvolutivePointedSemigroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A) 
      primT : ((Repr A) → (Repr A))  
  
 