
module LeftInverse   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftInverse  (A : Set) : Set where 
     field  
      inv : (A → A) 
      e : A 
      op : (A → (A → A)) 
      leftInverse_inv_op_e : ( {x : A} → (op x (inv x)) ≡ e)  
  
  open LeftInverse
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
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftInverse A1)) (Le2 : (LeftInverse A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-inv : ( {x1 : A1} → (hom ((inv Le1) x1)) ≡ ((inv Le2) (hom x1))) 
      pres-e : (hom (e Le1)) ≡ (e Le2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftInverse A1)) (Le2 : (LeftInverse A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Le1) x1) ((inv Le2) y1)))) 
      interp-e : (interp (e Le1) (e Le2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))  
  
  data LeftInverseLTerm   : Set where 
      invL : (LeftInverseLTerm → LeftInverseLTerm) 
      eL : LeftInverseLTerm 
      opL : (LeftInverseLTerm → (LeftInverseLTerm → LeftInverseLTerm))  
      
  data ClLeftInverseClTerm  (A : Set) : Set where 
      sing : (A → (ClLeftInverseClTerm A)) 
      invCl : ((ClLeftInverseClTerm A) → (ClLeftInverseClTerm A)) 
      eCl : (ClLeftInverseClTerm A) 
      opCl : ((ClLeftInverseClTerm A) → ((ClLeftInverseClTerm A) → (ClLeftInverseClTerm A)))  
      
  data OpLeftInverseOLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftInverseOLTerm n)) 
      invOL : ((OpLeftInverseOLTerm n) → (OpLeftInverseOLTerm n)) 
      eOL : (OpLeftInverseOLTerm n) 
      opOL : ((OpLeftInverseOLTerm n) → ((OpLeftInverseOLTerm n) → (OpLeftInverseOLTerm n)))  
      
  data OpLeftInverseOL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftInverseOL2Term2 n A)) 
      sing2 : (A → (OpLeftInverseOL2Term2 n A)) 
      invOL2 : ((OpLeftInverseOL2Term2 n A) → (OpLeftInverseOL2Term2 n A)) 
      eOL2 : (OpLeftInverseOL2Term2 n A) 
      opOL2 : ((OpLeftInverseOL2Term2 n A) → ((OpLeftInverseOL2Term2 n A) → (OpLeftInverseOL2Term2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClLeftInverseClTerm A) → (ClLeftInverseClTerm A)) 
  simplifyCl _ (invCl x1) = (invCl (simplifyCl _ x1))  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpLeftInverseOLTerm n) → (OpLeftInverseOLTerm n)) 
  simplifyOpB _ (invOL x1) = (invOL (simplifyOpB _ x1))  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpLeftInverseOL2Term2 n A) → (OpLeftInverseOL2Term2 n A)) 
  simplifyOp _ _ (invOL2 x1) = (invOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftInverse A) → (LeftInverseLTerm → A)) 
  evalB Le (invL x1) = ((inv Le) (evalB Le x1))  
  evalB Le eL = (e Le)  
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftInverse A) → ((ClLeftInverseClTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (invCl x1) = ((inv Le) (evalCl Le x1))  
  evalCl Le eCl = (e Le)  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((LeftInverse A) → ((Vec A n) → ((OpLeftInverseOLTerm n) → A))) 
  evalOpB n Le vars (v x1) = (lookup vars x1)  
  evalOpB n Le vars (invOL x1) = ((inv Le) (evalOpB n Le vars x1))  
  evalOpB n Le vars eOL = (e Le)  
  evalOpB n Le vars (opOL x1 x2) = ((op Le) (evalOpB n Le vars x1) (evalOpB n Le vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((LeftInverse A) → ((Vec A n) → ((OpLeftInverseOL2Term2 n A) → A))) 
  evalOp n Le vars (v2 x1) = (lookup vars x1)  
  evalOp n Le vars (sing2 x1) = x1  
  evalOp n Le vars (invOL2 x1) = ((inv Le) (evalOp n Le vars x1))  
  evalOp n Le vars eOL2 = (e Le)  
  evalOp n Le vars (opOL2 x1 x2) = ((op Le) (evalOp n Le vars x1) (evalOp n Le vars x2))  
  inductionB :  (P : (LeftInverseLTerm → Set)) →  (( (x1 : LeftInverseLTerm) → ((P x1) → (P (invL x1)))) → ((P eL) → (( (x1 x2 : LeftInverseLTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : LeftInverseLTerm) → (P x))))) 
  inductionB p pinvl pel popl (invL x1) = (pinvl _ (inductionB p pinvl pel popl x1))  
  inductionB p pinvl pel popl eL = pel  
  inductionB p pinvl pel popl (opL x1 x2) = (popl _ _ (inductionB p pinvl pel popl x1) (inductionB p pinvl pel popl x2))  
  inductionCl :  (A : Set) (P : ((ClLeftInverseClTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClLeftInverseClTerm A)) → ((P x1) → (P (invCl x1)))) → ((P eCl) → (( (x1 x2 : (ClLeftInverseClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClLeftInverseClTerm A)) → (P x)))))) 
  inductionCl _ p psing pinvcl pecl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pinvcl pecl popcl (invCl x1) = (pinvcl _ (inductionCl _ p psing pinvcl pecl popcl x1))  
  inductionCl _ p psing pinvcl pecl popcl eCl = pecl  
  inductionCl _ p psing pinvcl pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pinvcl pecl popcl x1) (inductionCl _ p psing pinvcl pecl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpLeftInverseOLTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpLeftInverseOLTerm n)) → ((P x1) → (P (invOL x1)))) → ((P eOL) → (( (x1 x2 : (OpLeftInverseOLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpLeftInverseOLTerm n)) → (P x)))))) 
  inductionOpB _ p pv pinvol peol popol (v x1) = (pv x1)  
  inductionOpB _ p pv pinvol peol popol (invOL x1) = (pinvol _ (inductionOpB _ p pv pinvol peol popol x1))  
  inductionOpB _ p pv pinvol peol popol eOL = peol  
  inductionOpB _ p pv pinvol peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv pinvol peol popol x1) (inductionOpB _ p pv pinvol peol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpLeftInverseOL2Term2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpLeftInverseOL2Term2 n A)) → ((P x1) → (P (invOL2 x1)))) → ((P eOL2) → (( (x1 x2 : (OpLeftInverseOL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpLeftInverseOL2Term2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1) = (pinvol2 _ (inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 x1))  
  inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 pinvol2 peol2 popol2 x2))  
  stageB :  (LeftInverseLTerm → (Staged LeftInverseLTerm))
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClLeftInverseClTerm A) → (Staged (ClLeftInverseClTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl _ x1))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpLeftInverseOLTerm n) → (Staged (OpLeftInverseOLTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB _ x1))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpLeftInverseOL2Term2 n A) → (Staged (OpLeftInverseOL2Term2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp _ _ x1))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      invT : ((Repr A) → (Repr A)) 
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 