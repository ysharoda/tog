
module QuasiInverse   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsQuasiInverse  (A : Set) (inv : (A → A)) (op : (A → (A → A))) : Set where 
     field  
      quasiInverse_inv_op_e : ( {x : A} → (op (op x (inv x)) x) ≡ x) 
      quasiRightInverse_inv_op_e : ( {x : A} → (op (op (inv x) x) (inv x)) ≡ (inv x))  
  
  record QuasiInverse  (A : Set) : Set where 
     field  
      inv : (A → A) 
      op : (A → (A → A)) 
      isQuasiInverse : (IsQuasiInverse A inv op)  
  
  open QuasiInverse
  record Sig  (AS : Set) : Set where 
     field  
      invS : (AS → AS) 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      invP : ((Prod A A) → (Prod A A)) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      quasiInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP (opP xP (invP xP)) xP) ≡ xP) 
      quasiRightInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP (opP (invP xP) xP) (invP xP)) ≡ (invP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Qu1 : (QuasiInverse A1)) (Qu2 : (QuasiInverse A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-inv : ( {x1 : A1} → (hom ((inv Qu1) x1)) ≡ ((inv Qu2) (hom x1))) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Qu1) x1 x2)) ≡ ((op Qu2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Qu1 : (QuasiInverse A1)) (Qu2 : (QuasiInverse A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Qu1) x1) ((inv Qu2) y1)))) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Qu1) x1 x2) ((op Qu2) y1 y2)))))  
  
  data QuasiInverseTerm   : Set where 
      invL : (QuasiInverseTerm → QuasiInverseTerm) 
      opL : (QuasiInverseTerm → (QuasiInverseTerm → QuasiInverseTerm))  
      
  data ClQuasiInverseTerm  (A : Set) : Set where 
      sing : (A → (ClQuasiInverseTerm A)) 
      invCl : ((ClQuasiInverseTerm A) → (ClQuasiInverseTerm A)) 
      opCl : ((ClQuasiInverseTerm A) → ((ClQuasiInverseTerm A) → (ClQuasiInverseTerm A)))  
      
  data OpQuasiInverseTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpQuasiInverseTerm n)) 
      invOL : ((OpQuasiInverseTerm n) → (OpQuasiInverseTerm n)) 
      opOL : ((OpQuasiInverseTerm n) → ((OpQuasiInverseTerm n) → (OpQuasiInverseTerm n)))  
      
  data OpQuasiInverseTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpQuasiInverseTerm2 n A)) 
      sing2 : (A → (OpQuasiInverseTerm2 n A)) 
      invOL2 : ((OpQuasiInverseTerm2 n A) → (OpQuasiInverseTerm2 n A)) 
      opOL2 : ((OpQuasiInverseTerm2 n A) → ((OpQuasiInverseTerm2 n A) → (OpQuasiInverseTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClQuasiInverseTerm A) → (ClQuasiInverseTerm A)) 
  simplifyCl _ (invCl x1) = (invCl (simplifyCl _ x1))  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpQuasiInverseTerm n) → (OpQuasiInverseTerm n)) 
  simplifyOpB _ (invOL x1) = (invOL (simplifyOpB _ x1))  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpQuasiInverseTerm2 n A) → (OpQuasiInverseTerm2 n A)) 
  simplifyOp _ _ (invOL2 x1) = (invOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((QuasiInverse A) → (QuasiInverseTerm → A)) 
  evalB Qu (invL x1) = ((inv Qu) (evalB Qu x1))  
  evalB Qu (opL x1 x2) = ((op Qu) (evalB Qu x1) (evalB Qu x2))  
  evalCl :  {A : Set} →  ((QuasiInverse A) → ((ClQuasiInverseTerm A) → A)) 
  evalCl Qu (sing x1) = x1  
  evalCl Qu (invCl x1) = ((inv Qu) (evalCl Qu x1))  
  evalCl Qu (opCl x1 x2) = ((op Qu) (evalCl Qu x1) (evalCl Qu x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((QuasiInverse A) → ((Vec A n) → ((OpQuasiInverseTerm n) → A))) 
  evalOpB n Qu vars (v x1) = (lookup vars x1)  
  evalOpB n Qu vars (invOL x1) = ((inv Qu) (evalOpB n Qu vars x1))  
  evalOpB n Qu vars (opOL x1 x2) = ((op Qu) (evalOpB n Qu vars x1) (evalOpB n Qu vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((QuasiInverse A) → ((Vec A n) → ((OpQuasiInverseTerm2 n A) → A))) 
  evalOp n Qu vars (v2 x1) = (lookup vars x1)  
  evalOp n Qu vars (sing2 x1) = x1  
  evalOp n Qu vars (invOL2 x1) = ((inv Qu) (evalOp n Qu vars x1))  
  evalOp n Qu vars (opOL2 x1 x2) = ((op Qu) (evalOp n Qu vars x1) (evalOp n Qu vars x2))  
  inductionB :  (P : (QuasiInverseTerm → Set)) →  (( (x1 : QuasiInverseTerm) → ((P x1) → (P (invL x1)))) → (( (x1 x2 : QuasiInverseTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : QuasiInverseTerm) → (P x)))) 
  inductionB p pinvl popl (invL x1) = (pinvl _ (inductionB p pinvl popl x1))  
  inductionB p pinvl popl (opL x1 x2) = (popl _ _ (inductionB p pinvl popl x1) (inductionB p pinvl popl x2))  
  inductionCl :  (A : Set) (P : ((ClQuasiInverseTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClQuasiInverseTerm A)) → ((P x1) → (P (invCl x1)))) → (( (x1 x2 : (ClQuasiInverseTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClQuasiInverseTerm A)) → (P x))))) 
  inductionCl _ p psing pinvcl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pinvcl popcl (invCl x1) = (pinvcl _ (inductionCl _ p psing pinvcl popcl x1))  
  inductionCl _ p psing pinvcl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pinvcl popcl x1) (inductionCl _ p psing pinvcl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpQuasiInverseTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpQuasiInverseTerm n)) → ((P x1) → (P (invOL x1)))) → (( (x1 x2 : (OpQuasiInverseTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpQuasiInverseTerm n)) → (P x))))) 
  inductionOpB _ p pv pinvol popol (v x1) = (pv x1)  
  inductionOpB _ p pv pinvol popol (invOL x1) = (pinvol _ (inductionOpB _ p pv pinvol popol x1))  
  inductionOpB _ p pv pinvol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv pinvol popol x1) (inductionOpB _ p pv pinvol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpQuasiInverseTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpQuasiInverseTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → (( (x1 x2 : (OpQuasiInverseTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpQuasiInverseTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 pinvol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pinvol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pinvol2 popol2 (invOL2 x1) = (pinvol2 _ (inductionOp _ _ p pv2 psing2 pinvol2 popol2 x1))  
  inductionOp _ _ p pv2 psing2 pinvol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 pinvol2 popol2 x1) (inductionOp _ _ p pv2 psing2 pinvol2 popol2 x2))  
  stageB :  (QuasiInverseTerm → (Staged QuasiInverseTerm))
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClQuasiInverseTerm A) → (Staged (ClQuasiInverseTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl _ x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpQuasiInverseTerm n) → (Staged (OpQuasiInverseTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB _ x1))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpQuasiInverseTerm2 n A) → (Staged (OpQuasiInverseTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp _ _ x1))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      invT : ((Repr A) → (Repr A)) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 