
module InvolutiveRingoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveRingoid  (A : Set) (prim : (A → A)) (1ᵢ : A) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      fixes_prim_1ᵢ : (prim 1ᵢ) ≡ 1ᵢ 
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      antidis_prim_+ : ( {x y : A} → (prim (+ x y)) ≡ (+ (prim y) (prim x))) 
      antidis_prim_* : ( {x y : A} → (prim (* x y)) ≡ (* (prim y) (prim x)))  
  
  record InvolutiveRingoid  (A : Set) : Set where 
     field  
      prim : (A → A) 
      1ᵢ : A 
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isInvolutiveRingoid : (IsInvolutiveRingoid A prim 1ᵢ (*) (+))  
  
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
      
  simplifyCl :  (A : Set) →  ((ClInvolutiveRingoidTerm A) → (ClInvolutiveRingoidTerm A)) 
  simplifyCl _ (primCl 1Cl) = 1Cl  
  simplifyCl _ (primCl (primCl x)) = x  
  simplifyCl _ (+Cl (primCl y) (primCl x)) = (primCl (+Cl x y))  
  simplifyCl _ (*Cl (primCl y) (primCl x)) = (primCl (*Cl x y))  
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpInvolutiveRingoidTerm n) → (OpInvolutiveRingoidTerm n)) 
  simplifyOpB _ (primOL 1OL) = 1OL  
  simplifyOpB _ (primOL (primOL x)) = x  
  simplifyOpB _ (+OL (primOL y) (primOL x)) = (primOL (+OL x y))  
  simplifyOpB _ (*OL (primOL y) (primOL x)) = (primOL (*OL x y))  
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpInvolutiveRingoidTerm2 n A) → (OpInvolutiveRingoidTerm2 n A)) 
  simplifyOp _ _ (primOL2 1OL2) = 1OL2  
  simplifyOp _ _ (primOL2 (primOL2 x)) = x  
  simplifyOp _ _ (+OL2 (primOL2 y) (primOL2 x)) = (primOL2 (+OL2 x y))  
  simplifyOp _ _ (*OL2 (primOL2 y) (primOL2 x)) = (primOL2 (*OL2 x y))  
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
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
  evalOpB :  {A : Set} (n : Nat) →  ((InvolutiveRingoid A) → ((Vec A n) → ((OpInvolutiveRingoidTerm n) → A))) 
  evalOpB n In vars (v x1) = (lookup vars x1)  
  evalOpB n In vars (primOL x1) = ((prim In) (evalOpB n In vars x1))  
  evalOpB n In vars 1OL = (1ᵢ In)  
  evalOpB n In vars (*OL x1 x2) = ((* In) (evalOpB n In vars x1) (evalOpB n In vars x2))  
  evalOpB n In vars (+OL x1 x2) = ((+ In) (evalOpB n In vars x1) (evalOpB n In vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((InvolutiveRingoid A) → ((Vec A n) → ((OpInvolutiveRingoidTerm2 n A) → A))) 
  evalOp n In vars (v2 x1) = (lookup vars x1)  
  evalOp n In vars (sing2 x1) = x1  
  evalOp n In vars (primOL2 x1) = ((prim In) (evalOp n In vars x1))  
  evalOp n In vars 1OL2 = (1ᵢ In)  
  evalOp n In vars (*OL2 x1 x2) = ((* In) (evalOp n In vars x1) (evalOp n In vars x2))  
  evalOp n In vars (+OL2 x1 x2) = ((+ In) (evalOp n In vars x1) (evalOp n In vars x2))  
  inductionB :  (P : (InvolutiveRingoidTerm → Set)) →  (( (x1 : InvolutiveRingoidTerm) → ((P x1) → (P (primL x1)))) → ((P 1L) → (( (x1 x2 : InvolutiveRingoidTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : InvolutiveRingoidTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : InvolutiveRingoidTerm) → (P x)))))) 
  inductionB p ppriml p1l p*l p+l (primL x1) = (ppriml _ (inductionB p ppriml p1l p*l p+l x1))  
  inductionB p ppriml p1l p*l p+l 1L = p1l  
  inductionB p ppriml p1l p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p ppriml p1l p*l p+l x1) (inductionB p ppriml p1l p*l p+l x2))  
  inductionB p ppriml p1l p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p ppriml p1l p*l p+l x1) (inductionB p ppriml p1l p*l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClInvolutiveRingoidTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInvolutiveRingoidTerm A)) → ((P x1) → (P (primCl x1)))) → ((P 1Cl) → (( (x1 x2 : (ClInvolutiveRingoidTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClInvolutiveRingoidTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClInvolutiveRingoidTerm A)) → (P x))))))) 
  inductionCl _ p psing pprimcl p1cl p*cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing pprimcl p1cl p*cl p+cl (primCl x1) = (pprimcl _ (inductionCl _ p psing pprimcl p1cl p*cl p+cl x1))  
  inductionCl _ p psing pprimcl p1cl p*cl p+cl 1Cl = p1cl  
  inductionCl _ p psing pprimcl p1cl p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing pprimcl p1cl p*cl p+cl x1) (inductionCl _ p psing pprimcl p1cl p*cl p+cl x2))  
  inductionCl _ p psing pprimcl p1cl p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing pprimcl p1cl p*cl p+cl x1) (inductionCl _ p psing pprimcl p1cl p*cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpInvolutiveRingoidTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInvolutiveRingoidTerm n)) → ((P x1) → (P (primOL x1)))) → ((P 1OL) → (( (x1 x2 : (OpInvolutiveRingoidTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpInvolutiveRingoidTerm n)) → (P x))))))) 
  inductionOpB _ p pv pprimol p1ol p*ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv pprimol p1ol p*ol p+ol (primOL x1) = (pprimol _ (inductionOpB _ p pv pprimol p1ol p*ol p+ol x1))  
  inductionOpB _ p pv pprimol p1ol p*ol p+ol 1OL = p1ol  
  inductionOpB _ p pv pprimol p1ol p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv pprimol p1ol p*ol p+ol x1) (inductionOpB _ p pv pprimol p1ol p*ol p+ol x2))  
  inductionOpB _ p pv pprimol p1ol p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv pprimol p1ol p*ol p+ol x1) (inductionOpB _ p pv pprimol p1ol p*ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpInvolutiveRingoidTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInvolutiveRingoidTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ((P 1OL2) → (( (x1 x2 : (OpInvolutiveRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpInvolutiveRingoidTerm2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x1))  
  inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 1OL2 = p1ol2  
  inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 pprimol2 p1ol2 p*ol2 p+ol2 x2))  
  stageB :  (InvolutiveRingoidTerm → (Staged InvolutiveRingoidTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB 1L = (Now 1L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClInvolutiveRingoidTerm A) → (Staged (ClInvolutiveRingoidTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpInvolutiveRingoidTerm n) → (Staged (OpInvolutiveRingoidTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpInvolutiveRingoidTerm2 n A) → (Staged (OpInvolutiveRingoidTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      1T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 