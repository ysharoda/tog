
module InvolutiveRingoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveRingoid  (A : Set) : Set where 
     field  
      prim : (A → A) 
      1ᵢ : A 
      fixes_prim_1ᵢ : (prim 1ᵢ) ≡ 1ᵢ 
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x) 
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      antidis_prim_+ : ( {x y : A} → (prim (+ x y)) ≡ (+ (prim y) (prim x))) 
      antidis_prim_* : ( {x y : A} → (prim (* x y)) ≡ (* (prim y) (prim x)))  
  
  open InvolutiveRingoid
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      1S : AS 
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      1P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      fixes_prim_1P : (primP 1P) ≡ 1P 
      involutive_primP : ( {xP : (Prod A A)} → (primP (primP xP)) ≡ xP) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      antidis_prim_+P : ( {xP yP : (Prod A A)} → (primP (+P xP yP)) ≡ (+P (primP yP) (primP xP))) 
      antidis_prim_*P : ( {xP yP : (Prod A A)} → (primP (*P xP yP)) ≡ (*P (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRingoid A1)) (In2 : (InvolutiveRingoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1))) 
      pres-1 : (hom (1ᵢ In1)) ≡ (1ᵢ In2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* In1) x1 x2)) ≡ ((* In2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ In1) x1 x2)) ≡ ((+ In2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRingoid A1)) (In2 : (InvolutiveRingoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))) 
      interp-1 : (interp (1ᵢ In1) (1ᵢ In2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* In1) x1 x2) ((* In2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ In1) x1 x2) ((+ In2) y1 y2)))))  
  
  data InvolutiveRingoidTerm   : Set where 
      primL : (InvolutiveRingoidTerm → InvolutiveRingoidTerm) 
      1L : InvolutiveRingoidTerm 
      *L : (InvolutiveRingoidTerm → (InvolutiveRingoidTerm → InvolutiveRingoidTerm)) 
      +L : (InvolutiveRingoidTerm → (InvolutiveRingoidTerm → InvolutiveRingoidTerm))  
      
  data ClInvolutiveRingoidTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveRingoidTerm A)) 
      primCl : ((ClInvolutiveRingoidTerm A) → (ClInvolutiveRingoidTerm A)) 
      1Cl : (ClInvolutiveRingoidTerm A) 
      *Cl : ((ClInvolutiveRingoidTerm A) → ((ClInvolutiveRingoidTerm A) → (ClInvolutiveRingoidTerm A))) 
      +Cl : ((ClInvolutiveRingoidTerm A) → ((ClInvolutiveRingoidTerm A) → (ClInvolutiveRingoidTerm A)))  
      
  data OpInvolutiveRingoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveRingoidTerm n)) 
      primOL : ((OpInvolutiveRingoidTerm n) → (OpInvolutiveRingoidTerm n)) 
      1OL : (OpInvolutiveRingoidTerm n) 
      *OL : ((OpInvolutiveRingoidTerm n) → ((OpInvolutiveRingoidTerm n) → (OpInvolutiveRingoidTerm n))) 
      +OL : ((OpInvolutiveRingoidTerm n) → ((OpInvolutiveRingoidTerm n) → (OpInvolutiveRingoidTerm n)))  
      
  data OpInvolutiveRingoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveRingoidTerm2 n A)) 
      sing2 : (A → (OpInvolutiveRingoidTerm2 n A)) 
      primOL2 : ((OpInvolutiveRingoidTerm2 n A) → (OpInvolutiveRingoidTerm2 n A)) 
      1OL2 : (OpInvolutiveRingoidTerm2 n A) 
      *OL2 : ((OpInvolutiveRingoidTerm2 n A) → ((OpInvolutiveRingoidTerm2 n A) → (OpInvolutiveRingoidTerm2 n A))) 
      +OL2 : ((OpInvolutiveRingoidTerm2 n A) → ((OpInvolutiveRingoidTerm2 n A) → (OpInvolutiveRingoidTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveRingoidTerm A) → (ClInvolutiveRingoidTerm A)) 
  simplifyCl (primCl 1Cl) = 1Cl  
  simplifyCl (primCl (primCl x)) = x  
  simplifyCl (+Cl (primCl y) (primCl x)) = (primCl (+Cl x y))  
  simplifyCl (*Cl (primCl y) (primCl x)) = (primCl (*Cl x y))  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveRingoidTerm n) → (OpInvolutiveRingoidTerm n)) 
  simplifyOpB (primOL 1OL) = 1OL  
  simplifyOpB (primOL (primOL x)) = x  
  simplifyOpB (+OL (primOL y) (primOL x)) = (primOL (+OL x y))  
  simplifyOpB (*OL (primOL y) (primOL x)) = (primOL (*OL x y))  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingoidTerm2 n A) → (OpInvolutiveRingoidTerm2 n A)) 
  simplifyOp (primOL2 1OL2) = 1OL2  
  simplifyOp (primOL2 (primOL2 x)) = x  
  simplifyOp (+OL2 (primOL2 y) (primOL2 x)) = (primOL2 (+OL2 x y))  
  simplifyOp (*OL2 (primOL2 y) (primOL2 x)) = (primOL2 (*OL2 x y))  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveRingoid A) → (InvolutiveRingoidTerm → A)) 
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalB In 1L = (1ᵢ In)  
  evalB In (*L x1 x2) = ((* In) (evalB In x1) (evalB In x2))  
  evalB In (+L x1 x2) = ((+ In) (evalB In x1) (evalB In x2))  
  evalCl :  {A : Set} →  ((InvolutiveRingoid A) → ((ClInvolutiveRingoidTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalCl In 1Cl = (1ᵢ In)  
  evalCl In (*Cl x1 x2) = ((* In) (evalCl In x1) (evalCl In x2))  
  evalCl In (+Cl x1 x2) = ((+ In) (evalCl In x1) (evalCl In x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveRingoid A) → ((Vec A n) → ((OpInvolutiveRingoidTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOpB In vars 1OL = (1ᵢ In)  
  evalOpB In vars (*OL x1 x2) = ((* In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars (+OL x1 x2) = ((+ In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveRingoid A) → ((Vec A n) → ((OpInvolutiveRingoidTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  evalOp In vars 1OL2 = (1ᵢ In)  
  evalOp In vars (*OL2 x1 x2) = ((* In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars (+OL2 x1 x2) = ((+ In) (evalOp In vars x1) (evalOp In vars x2))  
  inductionB :  {P : (InvolutiveRingoidTerm → Set)} →  (( (x1 : InvolutiveRingoidTerm) → ((P x1) → (P (primL x1)))) → ((P 1L) → (( (x1 x2 : InvolutiveRingoidTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : InvolutiveRingoidTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : InvolutiveRingoidTerm) → (P x)))))) 
  inductionB ppriml p1l p*l p+l (primL x1) = (ppriml _ (inductionB ppriml p1l p*l p+l x1))  
  inductionB ppriml p1l p*l p+l 1L = p1l  
  inductionB ppriml p1l p*l p+l (*L x1 x2) = (p*l _ _ (inductionB ppriml p1l p*l p+l x1) (inductionB ppriml p1l p*l p+l x2))  
  inductionB ppriml p1l p*l p+l (+L x1 x2) = (p+l _ _ (inductionB ppriml p1l p*l p+l x1) (inductionB ppriml p1l p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClInvolutiveRingoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInvolutiveRingoidTerm A)) → ((P x1) → (P (primCl x1)))) → ((P 1Cl) → (( (x1 x2 : (ClInvolutiveRingoidTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClInvolutiveRingoidTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClInvolutiveRingoidTerm A)) → (P x))))))) 
  inductionCl psing pprimcl p1cl p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing pprimcl p1cl p*cl p+cl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl p1cl p*cl p+cl x1))  
  inductionCl psing pprimcl p1cl p*cl p+cl 1Cl = p1cl  
  inductionCl psing pprimcl p1cl p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing pprimcl p1cl p*cl p+cl x1) (inductionCl psing pprimcl p1cl p*cl p+cl x2))  
  inductionCl psing pprimcl p1cl p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing pprimcl p1cl p*cl p+cl x1) (inductionCl psing pprimcl p1cl p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveRingoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInvolutiveRingoidTerm n)) → ((P x1) → (P (primOL x1)))) → ((P 1OL) → (( (x1 x2 : (OpInvolutiveRingoidTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpInvolutiveRingoidTerm n)) → (P x))))))) 
  inductionOpB pv pprimol p1ol p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv pprimol p1ol p*ol p+ol (primOL x1) = (pprimol _ (inductionOpB pv pprimol p1ol p*ol p+ol x1))  
  inductionOpB pv pprimol p1ol p*ol p+ol 1OL = p1ol  
  inductionOpB pv pprimol p1ol p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv pprimol p1ol p*ol p+ol x1) (inductionOpB pv pprimol p1ol p*ol p+ol x2))  
  inductionOpB pv pprimol p1ol p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv pprimol p1ol p*ol p+ol x1) (inductionOpB pv pprimol p1ol p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveRingoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInvolutiveRingoidTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ((P 1OL2) → (( (x1 x2 : (OpInvolutiveRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpInvolutiveRingoidTerm2 n A)) → (P x)))))))) 
  inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x1))  
  inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x2))  
  stageB :  (InvolutiveRingoidTerm → (Staged InvolutiveRingoidTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB 1L = (Now 1L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClInvolutiveRingoidTerm A) → (Staged (ClInvolutiveRingoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpInvolutiveRingoidTerm n) → (Staged (OpInvolutiveRingoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingoidTerm2 n A) → (Staged (OpInvolutiveRingoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      1T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 