
module InvolutiveRingoidSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveRingoidSig  (A : Set) (prim : (A → A)) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
    
  record InvolutiveRingoidSig  (A : Set) : Set where 
     field  
      prim : (A → A) 
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isInvolutiveRingoidSig : (IsInvolutiveRingoidSig A prim (*) (+))  
  
  open InvolutiveRingoidSig
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRingoidSig A1)) (In2 : (InvolutiveRingoidSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* In1) x1 x2)) ≡ ((* In2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ In1) x1 x2)) ≡ ((+ In2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRingoidSig A1)) (In2 : (InvolutiveRingoidSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* In1) x1 x2) ((* In2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ In1) x1 x2) ((+ In2) y1 y2)))))  
  
  data InvolutiveRingoidSigTerm   : Set where 
      primL : (InvolutiveRingoidSigTerm → InvolutiveRingoidSigTerm) 
      *L : (InvolutiveRingoidSigTerm → (InvolutiveRingoidSigTerm → InvolutiveRingoidSigTerm)) 
      +L : (InvolutiveRingoidSigTerm → (InvolutiveRingoidSigTerm → InvolutiveRingoidSigTerm))  
      
  data ClInvolutiveRingoidSigTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveRingoidSigTerm A)) 
      primCl : ((ClInvolutiveRingoidSigTerm A) → (ClInvolutiveRingoidSigTerm A)) 
      *Cl : ((ClInvolutiveRingoidSigTerm A) → ((ClInvolutiveRingoidSigTerm A) → (ClInvolutiveRingoidSigTerm A))) 
      +Cl : ((ClInvolutiveRingoidSigTerm A) → ((ClInvolutiveRingoidSigTerm A) → (ClInvolutiveRingoidSigTerm A)))  
      
  data OpInvolutiveRingoidSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveRingoidSigTerm n)) 
      primOL : ((OpInvolutiveRingoidSigTerm n) → (OpInvolutiveRingoidSigTerm n)) 
      *OL : ((OpInvolutiveRingoidSigTerm n) → ((OpInvolutiveRingoidSigTerm n) → (OpInvolutiveRingoidSigTerm n))) 
      +OL : ((OpInvolutiveRingoidSigTerm n) → ((OpInvolutiveRingoidSigTerm n) → (OpInvolutiveRingoidSigTerm n)))  
      
  data OpInvolutiveRingoidSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveRingoidSigTerm2 n A)) 
      sing2 : (A → (OpInvolutiveRingoidSigTerm2 n A)) 
      primOL2 : ((OpInvolutiveRingoidSigTerm2 n A) → (OpInvolutiveRingoidSigTerm2 n A)) 
      *OL2 : ((OpInvolutiveRingoidSigTerm2 n A) → ((OpInvolutiveRingoidSigTerm2 n A) → (OpInvolutiveRingoidSigTerm2 n A))) 
      +OL2 : ((OpInvolutiveRingoidSigTerm2 n A) → ((OpInvolutiveRingoidSigTerm2 n A) → (OpInvolutiveRingoidSigTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveRingoidSigTerm A) → (ClInvolutiveRingoidSigTerm A)) 
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveRingoidSigTerm n) → (OpInvolutiveRingoidSigTerm n)) 
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingoidSigTerm2 n A) → (OpInvolutiveRingoidSigTerm2 n A)) 
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveRingoidSig A) → (InvolutiveRingoidSigTerm → A)) 
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalB In (*L x1 x2) = ((* In) (evalB In x1) (evalB In x2))  
  evalB In (+L x1 x2) = ((+ In) (evalB In x1) (evalB In x2))  
  evalCl :  {A : Set} →  ((InvolutiveRingoidSig A) → ((ClInvolutiveRingoidSigTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalCl In (*Cl x1 x2) = ((* In) (evalCl In x1) (evalCl In x2))  
  evalCl In (+Cl x1 x2) = ((+ In) (evalCl In x1) (evalCl In x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveRingoidSig A) → ((Vec A n) → ((OpInvolutiveRingoidSigTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOpB In vars (*OL x1 x2) = ((* In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars (+OL x1 x2) = ((+ In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveRingoidSig A) → ((Vec A n) → ((OpInvolutiveRingoidSigTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  evalOp In vars (*OL2 x1 x2) = ((* In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars (+OL2 x1 x2) = ((+ In) (evalOp In vars x1) (evalOp In vars x2))  
  inductionB :  {P : (InvolutiveRingoidSigTerm → Set)} →  (( (x1 : InvolutiveRingoidSigTerm) → ((P x1) → (P (primL x1)))) → (( (x1 x2 : InvolutiveRingoidSigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : InvolutiveRingoidSigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : InvolutiveRingoidSigTerm) → (P x))))) 
  inductionB ppriml p*l p+l (primL x1) = (ppriml _ (inductionB ppriml p*l p+l x1))  
  inductionB ppriml p*l p+l (*L x1 x2) = (p*l _ _ (inductionB ppriml p*l p+l x1) (inductionB ppriml p*l p+l x2))  
  inductionB ppriml p*l p+l (+L x1 x2) = (p+l _ _ (inductionB ppriml p*l p+l x1) (inductionB ppriml p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClInvolutiveRingoidSigTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInvolutiveRingoidSigTerm A)) → ((P x1) → (P (primCl x1)))) → (( (x1 x2 : (ClInvolutiveRingoidSigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClInvolutiveRingoidSigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClInvolutiveRingoidSigTerm A)) → (P x)))))) 
  inductionCl psing pprimcl p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing pprimcl p*cl p+cl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl p*cl p+cl x1))  
  inductionCl psing pprimcl p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing pprimcl p*cl p+cl x1) (inductionCl psing pprimcl p*cl p+cl x2))  
  inductionCl psing pprimcl p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing pprimcl p*cl p+cl x1) (inductionCl psing pprimcl p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveRingoidSigTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInvolutiveRingoidSigTerm n)) → ((P x1) → (P (primOL x1)))) → (( (x1 x2 : (OpInvolutiveRingoidSigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidSigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpInvolutiveRingoidSigTerm n)) → (P x)))))) 
  inductionOpB pv pprimol p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv pprimol p*ol p+ol (primOL x1) = (pprimol _ (inductionOpB pv pprimol p*ol p+ol x1))  
  inductionOpB pv pprimol p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv pprimol p*ol p+ol x1) (inductionOpB pv pprimol p*ol p+ol x2))  
  inductionOpB pv pprimol p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv pprimol p*ol p+ol x1) (inductionOpB pv pprimol p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveRingoidSigTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInvolutiveRingoidSigTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → (( (x1 x2 : (OpInvolutiveRingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpInvolutiveRingoidSigTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 x1))  
  inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 pprimol2 p*ol2 p+ol2 x2))  
  stageB :  (InvolutiveRingoidSigTerm → (Staged InvolutiveRingoidSigTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClInvolutiveRingoidSigTerm A) → (Staged (ClInvolutiveRingoidSigTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpInvolutiveRingoidSigTerm n) → (Staged (OpInvolutiveRingoidSigTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingoidSigTerm2 n A) → (Staged (OpInvolutiveRingoidSigTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 