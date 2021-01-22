
module Inverse   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Inverse  (A : Set) : Set where 
     field  
      inv : (A → A) 
      e : A 
      op : (A → (A → A)) 
      leftInverse_inv_op_e : ( {x : A} → (op x (inv x)) ≡ e) 
      rightInverse_inv_op_e : ( {x : A} → (op (inv x) x) ≡ e)  
  
  open Inverse
  record Sig  (AS : Set) : Set where 
     field  
      invS : (AS → AS) 
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      invP : ((Prod A A) → (Prod A A)) 
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP xP (invP xP)) ≡ eP) 
      rightInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP (invP xP) xP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (Inverse A1)) (In2 : (Inverse A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-inv : ( {x1 : A1} → (hom ((inv In1) x1)) ≡ ((inv In2) (hom x1))) 
      pres-e : (hom (e In1)) ≡ (e In2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op In1) x1 x2)) ≡ ((op In2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (Inverse A1)) (In2 : (Inverse A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv In1) x1) ((inv In2) y1)))) 
      interp-e : (interp (e In1) (e In2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2)))))  
  
  data InverseLTerm   : Set where 
      invL : (InverseLTerm → InverseLTerm) 
      eL : InverseLTerm 
      opL : (InverseLTerm → (InverseLTerm → InverseLTerm))  
      
  data ClInverseClTerm  (A : Set) : Set where 
      sing : (A → (ClInverseClTerm A)) 
      invCl : ((ClInverseClTerm A) → (ClInverseClTerm A)) 
      eCl : (ClInverseClTerm A) 
      opCl : ((ClInverseClTerm A) → ((ClInverseClTerm A) → (ClInverseClTerm A)))  
      
  data OpInverseOLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInverseOLTerm n)) 
      invOL : ((OpInverseOLTerm n) → (OpInverseOLTerm n)) 
      eOL : (OpInverseOLTerm n) 
      opOL : ((OpInverseOLTerm n) → ((OpInverseOLTerm n) → (OpInverseOLTerm n)))  
      
  data OpInverseOL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInverseOL2Term2 n A)) 
      sing2 : (A → (OpInverseOL2Term2 n A)) 
      invOL2 : ((OpInverseOL2Term2 n A) → (OpInverseOL2Term2 n A)) 
      eOL2 : (OpInverseOL2Term2 n A) 
      opOL2 : ((OpInverseOL2Term2 n A) → ((OpInverseOL2Term2 n A) → (OpInverseOL2Term2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClInverseClTerm A) → (ClInverseClTerm A)) 
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl eCl = eCl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInverseOLTerm n) → (OpInverseOLTerm n)) 
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB eOL = eOL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInverseOL2Term2 n A) → (OpInverseOL2Term2 n A)) 
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Inverse A) → (InverseLTerm → A)) 
  evalB In (invL x1) = ((inv In) (evalB In x1))  
  evalB In eL = (e In)  
  evalB In (opL x1 x2) = ((op In) (evalB In x1) (evalB In x2))  
  evalCl :  {A : Set} →  ((Inverse A) → ((ClInverseClTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (invCl x1) = ((inv In) (evalCl In x1))  
  evalCl In eCl = (e In)  
  evalCl In (opCl x1 x2) = ((op In) (evalCl In x1) (evalCl In x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Inverse A) → ((Vec A n) → ((OpInverseOLTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (invOL x1) = ((inv In) (evalOpB In vars x1))  
  evalOpB In vars eOL = (e In)  
  evalOpB In vars (opOL x1 x2) = ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Inverse A) → ((Vec A n) → ((OpInverseOL2Term2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (invOL2 x1) = ((inv In) (evalOp In vars x1))  
  evalOp In vars eOL2 = (e In)  
  evalOp In vars (opOL2 x1 x2) = ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  inductionB :  {P : (InverseLTerm → Set)} →  (( (x1 : InverseLTerm) → ((P x1) → (P (invL x1)))) → ((P eL) → (( (x1 x2 : InverseLTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : InverseLTerm) → (P x))))) 
  inductionB pinvl pel popl (invL x1) = (pinvl _ (inductionB pinvl pel popl x1))  
  inductionB pinvl pel popl eL = pel  
  inductionB pinvl pel popl (opL x1 x2) = (popl _ _ (inductionB pinvl pel popl x1) (inductionB pinvl pel popl x2))  
  inductionCl :  {A : Set} {P : ((ClInverseClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInverseClTerm A)) → ((P x1) → (P (invCl x1)))) → ((P eCl) → (( (x1 x2 : (ClInverseClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClInverseClTerm A)) → (P x)))))) 
  inductionCl psing pinvcl pecl popcl (sing x1) = (psing x1)  
  inductionCl psing pinvcl pecl popcl (invCl x1) = (pinvcl _ (inductionCl psing pinvcl pecl popcl x1))  
  inductionCl psing pinvcl pecl popcl eCl = pecl  
  inductionCl psing pinvcl pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pinvcl pecl popcl x1) (inductionCl psing pinvcl pecl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpInverseOLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInverseOLTerm n)) → ((P x1) → (P (invOL x1)))) → ((P eOL) → (( (x1 x2 : (OpInverseOLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpInverseOLTerm n)) → (P x)))))) 
  inductionOpB pv pinvol peol popol (v x1) = (pv x1)  
  inductionOpB pv pinvol peol popol (invOL x1) = (pinvol _ (inductionOpB pv pinvol peol popol x1))  
  inductionOpB pv pinvol peol popol eOL = peol  
  inductionOpB pv pinvol peol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv pinvol peol popol x1) (inductionOpB pv pinvol peol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInverseOL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInverseOL2Term2 n A)) → ((P x1) → (P (invOL2 x1)))) → ((P eOL2) → (( (x1 x2 : (OpInverseOL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpInverseOL2Term2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 pinvol2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pinvol2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 pinvol2 peol2 popol2 x1))  
  inductionOp pv2 psing2 pinvol2 peol2 popol2 eOL2 = peol2  
  inductionOp pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 pinvol2 peol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 peol2 popol2 x2))  
  stageB :  (InverseLTerm → (Staged InverseLTerm))
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClInverseClTerm A) → (Staged (ClInverseClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageCl eCl = (Now eCl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpInverseOLTerm n) → (Staged (OpInverseOLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOpB eOL = (Now eOL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInverseOL2Term2 n A) → (Staged (OpInverseOL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      invT : ((Repr A) → (Repr A)) 
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 