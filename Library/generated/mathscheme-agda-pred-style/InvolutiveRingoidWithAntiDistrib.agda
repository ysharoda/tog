
module InvolutiveRingoidWithAntiDistrib   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveRingoidWithAntiDistrib  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) (prim : (A → A)) : Set where 
     field  
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      antidis_prim_+ : ( {x y : A} → (prim (+ x y)) ≡ (+ (prim y) (prim x))) 
      antidis_prim_* : ( {x y : A} → (prim (* x y)) ≡ (* (prim y) (prim x)))  
  
  record InvolutiveRingoidWithAntiDistrib  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      prim : (A → A) 
      isInvolutiveRingoidWithAntiDistrib : (IsInvolutiveRingoidWithAntiDistrib A (*) (+) prim)  
  
  open InvolutiveRingoidWithAntiDistrib
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      primP : ((Prod A A) → (Prod A A)) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      antidis_prim_+P : ( {xP yP : (Prod A A)} → (primP (+P xP yP)) ≡ (+P (primP yP) (primP xP))) 
      antidis_prim_*P : ( {xP yP : (Prod A A)} → (primP (*P xP yP)) ≡ (*P (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRingoidWithAntiDistrib A1)) (In2 : (InvolutiveRingoidWithAntiDistrib A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* In1) x1 x2)) ≡ ((* In2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ In1) x1 x2)) ≡ ((+ In2) (hom x1) (hom x2))) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRingoidWithAntiDistrib A1)) (In2 : (InvolutiveRingoidWithAntiDistrib A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* In1) x1 x2) ((* In2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ In1) x1 x2) ((+ In2) y1 y2))))) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))  
  
  data InvolutiveRingoidWithAntiDistribTerm   : Set where 
      *L : (InvolutiveRingoidWithAntiDistribTerm → (InvolutiveRingoidWithAntiDistribTerm → InvolutiveRingoidWithAntiDistribTerm)) 
      +L : (InvolutiveRingoidWithAntiDistribTerm → (InvolutiveRingoidWithAntiDistribTerm → InvolutiveRingoidWithAntiDistribTerm)) 
      primL : (InvolutiveRingoidWithAntiDistribTerm → InvolutiveRingoidWithAntiDistribTerm)  
      
  data ClInvolutiveRingoidWithAntiDistribTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveRingoidWithAntiDistribTerm A)) 
      *Cl : ((ClInvolutiveRingoidWithAntiDistribTerm A) → ((ClInvolutiveRingoidWithAntiDistribTerm A) → (ClInvolutiveRingoidWithAntiDistribTerm A))) 
      +Cl : ((ClInvolutiveRingoidWithAntiDistribTerm A) → ((ClInvolutiveRingoidWithAntiDistribTerm A) → (ClInvolutiveRingoidWithAntiDistribTerm A))) 
      primCl : ((ClInvolutiveRingoidWithAntiDistribTerm A) → (ClInvolutiveRingoidWithAntiDistribTerm A))  
      
  data OpInvolutiveRingoidWithAntiDistribTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveRingoidWithAntiDistribTerm n)) 
      *OL : ((OpInvolutiveRingoidWithAntiDistribTerm n) → ((OpInvolutiveRingoidWithAntiDistribTerm n) → (OpInvolutiveRingoidWithAntiDistribTerm n))) 
      +OL : ((OpInvolutiveRingoidWithAntiDistribTerm n) → ((OpInvolutiveRingoidWithAntiDistribTerm n) → (OpInvolutiveRingoidWithAntiDistribTerm n))) 
      primOL : ((OpInvolutiveRingoidWithAntiDistribTerm n) → (OpInvolutiveRingoidWithAntiDistribTerm n))  
      
  data OpInvolutiveRingoidWithAntiDistribTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) 
      sing2 : (A → (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) 
      *OL2 : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A))) 
      +OL2 : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A))) 
      primOL2 : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveRingoidWithAntiDistribTerm A) → (ClInvolutiveRingoidWithAntiDistribTerm A)) 
  simplifyCl (+Cl (primCl y) (primCl x)) = (primCl (+Cl x y))  
  simplifyCl (*Cl (primCl y) (primCl x)) = (primCl (*Cl x y))  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveRingoidWithAntiDistribTerm n) → (OpInvolutiveRingoidWithAntiDistribTerm n)) 
  simplifyOpB (+OL (primOL y) (primOL x)) = (primOL (+OL x y))  
  simplifyOpB (*OL (primOL y) (primOL x)) = (primOL (*OL x y))  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) 
  simplifyOp (+OL2 (primOL2 y) (primOL2 x)) = (primOL2 (+OL2 x y))  
  simplifyOp (*OL2 (primOL2 y) (primOL2 x)) = (primOL2 (*OL2 x y))  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveRingoidWithAntiDistrib A) → (InvolutiveRingoidWithAntiDistribTerm → A)) 
  evalB In (*L x1 x2) = ((* In) (evalB In x1) (evalB In x2))  
  evalB In (+L x1 x2) = ((+ In) (evalB In x1) (evalB In x2))  
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InvolutiveRingoidWithAntiDistrib A) → ((ClInvolutiveRingoidWithAntiDistribTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (*Cl x1 x2) = ((* In) (evalCl In x1) (evalCl In x2))  
  evalCl In (+Cl x1 x2) = ((+ In) (evalCl In x1) (evalCl In x2))  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveRingoidWithAntiDistrib A) → ((Vec A n) → ((OpInvolutiveRingoidWithAntiDistribTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (*OL x1 x2) = ((* In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars (+OL x1 x2) = ((+ In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveRingoidWithAntiDistrib A) → ((Vec A n) → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (*OL2 x1 x2) = ((* In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars (+OL2 x1 x2) = ((+ In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  inductionB :  {P : (InvolutiveRingoidWithAntiDistribTerm → Set)} →  (( (x1 x2 : InvolutiveRingoidWithAntiDistribTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : InvolutiveRingoidWithAntiDistribTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 : InvolutiveRingoidWithAntiDistribTerm) → ((P x1) → (P (primL x1)))) → ( (x : InvolutiveRingoidWithAntiDistribTerm) → (P x))))) 
  inductionB p*l p+l ppriml (*L x1 x2) = (p*l _ _ (inductionB p*l p+l ppriml x1) (inductionB p*l p+l ppriml x2))  
  inductionB p*l p+l ppriml (+L x1 x2) = (p+l _ _ (inductionB p*l p+l ppriml x1) (inductionB p*l p+l ppriml x2))  
  inductionB p*l p+l ppriml (primL x1) = (ppriml _ (inductionB p*l p+l ppriml x1))  
  inductionCl :  {A : Set} {P : ((ClInvolutiveRingoidWithAntiDistribTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClInvolutiveRingoidWithAntiDistribTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClInvolutiveRingoidWithAntiDistribTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 : (ClInvolutiveRingoidWithAntiDistribTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClInvolutiveRingoidWithAntiDistribTerm A)) → (P x)))))) 
  inductionCl psing p*cl p+cl pprimcl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl pprimcl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl pprimcl x1) (inductionCl psing p*cl p+cl pprimcl x2))  
  inductionCl psing p*cl p+cl pprimcl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl pprimcl x1) (inductionCl psing p*cl p+cl pprimcl x2))  
  inductionCl psing p*cl p+cl pprimcl (primCl x1) = (pprimcl _ (inductionCl psing p*cl p+cl pprimcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveRingoidWithAntiDistribTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 : (OpInvolutiveRingoidWithAntiDistribTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpInvolutiveRingoidWithAntiDistribTerm n)) → (P x)))))) 
  inductionOpB pv p*ol p+ol pprimol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol pprimol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol pprimol x1) (inductionOpB pv p*ol p+ol pprimol x2))  
  inductionOpB pv p*ol p+ol pprimol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol pprimol x1) (inductionOpB pv p*ol p+ol pprimol x2))  
  inductionOpB pv p*ol p+ol pprimol (primOL x1) = (pprimol _ (inductionOpB pv p*ol p+ol pprimol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 p*ol2 p+ol2 pprimol2 x1))  
  stageB :  (InvolutiveRingoidWithAntiDistribTerm → (Staged InvolutiveRingoidWithAntiDistribTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClInvolutiveRingoidWithAntiDistribTerm A) → (Staged (ClInvolutiveRingoidWithAntiDistribTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpInvolutiveRingoidWithAntiDistribTerm n) → (Staged (OpInvolutiveRingoidWithAntiDistribTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (Staged (OpInvolutiveRingoidWithAntiDistribTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      primT : ((Repr A) → (Repr A))  
  
 