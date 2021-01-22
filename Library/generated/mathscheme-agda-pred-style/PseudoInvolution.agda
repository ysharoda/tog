
module PseudoInvolution   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPseudoInvolution  (A : Set) (inv : (A → A)) (op : (A → (A → A))) : Set where 
     field  
      quasiRightInverse_inv_op_e : ( {x : A} → (op (op (inv x) x) (inv x)) ≡ (inv x))  
  
  record PseudoInvolution  (A : Set) : Set where 
     field  
      inv : (A → A) 
      op : (A → (A → A)) 
      isPseudoInvolution : (IsPseudoInvolution A inv op)  
  
  open PseudoInvolution
  record Sig  (AS : Set) : Set where 
     field  
      invS : (AS → AS) 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      invP : ((Prod A A) → (Prod A A)) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      quasiRightInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP (opP (invP xP) xP) (invP xP)) ≡ (invP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ps1 : (PseudoInvolution A1)) (Ps2 : (PseudoInvolution A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-inv : ( {x1 : A1} → (hom ((inv Ps1) x1)) ≡ ((inv Ps2) (hom x1))) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ps1) x1 x2)) ≡ ((op Ps2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ps1 : (PseudoInvolution A1)) (Ps2 : (PseudoInvolution A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Ps1) x1) ((inv Ps2) y1)))) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ps1) x1 x2) ((op Ps2) y1 y2)))))  
  
  data PseudoInvolutionTerm   : Set where 
      invL : (PseudoInvolutionTerm → PseudoInvolutionTerm) 
      opL : (PseudoInvolutionTerm → (PseudoInvolutionTerm → PseudoInvolutionTerm))  
      
  data ClPseudoInvolutionTerm  (A : Set) : Set where 
      sing : (A → (ClPseudoInvolutionTerm A)) 
      invCl : ((ClPseudoInvolutionTerm A) → (ClPseudoInvolutionTerm A)) 
      opCl : ((ClPseudoInvolutionTerm A) → ((ClPseudoInvolutionTerm A) → (ClPseudoInvolutionTerm A)))  
      
  data OpPseudoInvolutionTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPseudoInvolutionTerm n)) 
      invOL : ((OpPseudoInvolutionTerm n) → (OpPseudoInvolutionTerm n)) 
      opOL : ((OpPseudoInvolutionTerm n) → ((OpPseudoInvolutionTerm n) → (OpPseudoInvolutionTerm n)))  
      
  data OpPseudoInvolutionTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPseudoInvolutionTerm2 n A)) 
      sing2 : (A → (OpPseudoInvolutionTerm2 n A)) 
      invOL2 : ((OpPseudoInvolutionTerm2 n A) → (OpPseudoInvolutionTerm2 n A)) 
      opOL2 : ((OpPseudoInvolutionTerm2 n A) → ((OpPseudoInvolutionTerm2 n A) → (OpPseudoInvolutionTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClPseudoInvolutionTerm A) → (ClPseudoInvolutionTerm A)) 
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPseudoInvolutionTerm n) → (OpPseudoInvolutionTerm n)) 
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPseudoInvolutionTerm2 n A) → (OpPseudoInvolutionTerm2 n A)) 
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PseudoInvolution A) → (PseudoInvolutionTerm → A)) 
  evalB Ps (invL x1) = ((inv Ps) (evalB Ps x1))  
  evalB Ps (opL x1 x2) = ((op Ps) (evalB Ps x1) (evalB Ps x2))  
  evalCl :  {A : Set} →  ((PseudoInvolution A) → ((ClPseudoInvolutionTerm A) → A)) 
  evalCl Ps (sing x1) = x1  
  evalCl Ps (invCl x1) = ((inv Ps) (evalCl Ps x1))  
  evalCl Ps (opCl x1 x2) = ((op Ps) (evalCl Ps x1) (evalCl Ps x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((PseudoInvolution A) → ((Vec A n) → ((OpPseudoInvolutionTerm n) → A))) 
  evalOpB Ps vars (v x1) = (lookup vars x1)  
  evalOpB Ps vars (invOL x1) = ((inv Ps) (evalOpB Ps vars x1))  
  evalOpB Ps vars (opOL x1 x2) = ((op Ps) (evalOpB Ps vars x1) (evalOpB Ps vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((PseudoInvolution A) → ((Vec A n) → ((OpPseudoInvolutionTerm2 n A) → A))) 
  evalOp Ps vars (v2 x1) = (lookup vars x1)  
  evalOp Ps vars (sing2 x1) = x1  
  evalOp Ps vars (invOL2 x1) = ((inv Ps) (evalOp Ps vars x1))  
  evalOp Ps vars (opOL2 x1 x2) = ((op Ps) (evalOp Ps vars x1) (evalOp Ps vars x2))  
  inductionB :  {P : (PseudoInvolutionTerm → Set)} →  (( (x1 : PseudoInvolutionTerm) → ((P x1) → (P (invL x1)))) → (( (x1 x2 : PseudoInvolutionTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : PseudoInvolutionTerm) → (P x)))) 
  inductionB pinvl popl (invL x1) = (pinvl _ (inductionB pinvl popl x1))  
  inductionB pinvl popl (opL x1 x2) = (popl _ _ (inductionB pinvl popl x1) (inductionB pinvl popl x2))  
  inductionCl :  {A : Set} {P : ((ClPseudoInvolutionTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClPseudoInvolutionTerm A)) → ((P x1) → (P (invCl x1)))) → (( (x1 x2 : (ClPseudoInvolutionTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClPseudoInvolutionTerm A)) → (P x))))) 
  inductionCl psing pinvcl popcl (sing x1) = (psing x1)  
  inductionCl psing pinvcl popcl (invCl x1) = (pinvcl _ (inductionCl psing pinvcl popcl x1))  
  inductionCl psing pinvcl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pinvcl popcl x1) (inductionCl psing pinvcl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpPseudoInvolutionTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpPseudoInvolutionTerm n)) → ((P x1) → (P (invOL x1)))) → (( (x1 x2 : (OpPseudoInvolutionTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpPseudoInvolutionTerm n)) → (P x))))) 
  inductionOpB pv pinvol popol (v x1) = (pv x1)  
  inductionOpB pv pinvol popol (invOL x1) = (pinvol _ (inductionOpB pv pinvol popol x1))  
  inductionOpB pv pinvol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv pinvol popol x1) (inductionOpB pv pinvol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPseudoInvolutionTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpPseudoInvolutionTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → (( (x1 x2 : (OpPseudoInvolutionTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpPseudoInvolutionTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 pinvol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pinvol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pinvol2 popol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 pinvol2 popol2 x1))  
  inductionOp pv2 psing2 pinvol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 pinvol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 popol2 x2))  
  stageB :  (PseudoInvolutionTerm → (Staged PseudoInvolutionTerm))
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClPseudoInvolutionTerm A) → (Staged (ClPseudoInvolutionTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpPseudoInvolutionTerm n) → (Staged (OpPseudoInvolutionTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpPseudoInvolutionTerm2 n A) → (Staged (OpPseudoInvolutionTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      invT : ((Repr A) → (Repr A)) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 