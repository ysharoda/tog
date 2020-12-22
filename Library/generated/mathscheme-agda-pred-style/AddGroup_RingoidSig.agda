
module AddGroup_RingoidSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAddGroup_RingoidSig  (A : Set) (+ : (A → (A → A))) (0ᵢ : A) (neg : (A → A)) (* : (A → (A → A))) : Set where 
     field  
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ)  
  
  record AddGroup_RingoidSig  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      0ᵢ : A 
      neg : (A → A) 
      * : (A → (A → A)) 
      isAddGroup_RingoidSig : (IsAddGroup_RingoidSig A (+) 0ᵢ neg (*))  
  
  open AddGroup_RingoidSig
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS)) 
      0S : AS 
      negS : (AS → AS) 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ad1 : (AddGroup_RingoidSig A1)) (Ad2 : (AddGroup_RingoidSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Ad1)) ≡ (0ᵢ Ad2) 
      pres-neg : ( {x1 : A1} → (hom ((neg Ad1) x1)) ≡ ((neg Ad2) (hom x1))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ad1) x1 x2)) ≡ ((* Ad2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ad1 : (AddGroup_RingoidSig A1)) (Ad2 : (AddGroup_RingoidSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Ad1) (0ᵢ Ad2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Ad1) x1) ((neg Ad2) y1)))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ad1) x1 x2) ((* Ad2) y1 y2)))))  
  
  data AddGroup_RingoidSigTerm   : Set where 
      +L : (AddGroup_RingoidSigTerm → (AddGroup_RingoidSigTerm → AddGroup_RingoidSigTerm)) 
      0L : AddGroup_RingoidSigTerm 
      negL : (AddGroup_RingoidSigTerm → AddGroup_RingoidSigTerm) 
      *L : (AddGroup_RingoidSigTerm → (AddGroup_RingoidSigTerm → AddGroup_RingoidSigTerm))  
      
  data ClAddGroup_RingoidSigTerm  (A : Set) : Set where 
      sing : (A → (ClAddGroup_RingoidSigTerm A)) 
      +Cl : ((ClAddGroup_RingoidSigTerm A) → ((ClAddGroup_RingoidSigTerm A) → (ClAddGroup_RingoidSigTerm A))) 
      0Cl : (ClAddGroup_RingoidSigTerm A) 
      negCl : ((ClAddGroup_RingoidSigTerm A) → (ClAddGroup_RingoidSigTerm A)) 
      *Cl : ((ClAddGroup_RingoidSigTerm A) → ((ClAddGroup_RingoidSigTerm A) → (ClAddGroup_RingoidSigTerm A)))  
      
  data OpAddGroup_RingoidSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAddGroup_RingoidSigTerm n)) 
      +OL : ((OpAddGroup_RingoidSigTerm n) → ((OpAddGroup_RingoidSigTerm n) → (OpAddGroup_RingoidSigTerm n))) 
      0OL : (OpAddGroup_RingoidSigTerm n) 
      negOL : ((OpAddGroup_RingoidSigTerm n) → (OpAddGroup_RingoidSigTerm n)) 
      *OL : ((OpAddGroup_RingoidSigTerm n) → ((OpAddGroup_RingoidSigTerm n) → (OpAddGroup_RingoidSigTerm n)))  
      
  data OpAddGroup_RingoidSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAddGroup_RingoidSigTerm2 n A)) 
      sing2 : (A → (OpAddGroup_RingoidSigTerm2 n A)) 
      +OL2 : ((OpAddGroup_RingoidSigTerm2 n A) → ((OpAddGroup_RingoidSigTerm2 n A) → (OpAddGroup_RingoidSigTerm2 n A))) 
      0OL2 : (OpAddGroup_RingoidSigTerm2 n A) 
      negOL2 : ((OpAddGroup_RingoidSigTerm2 n A) → (OpAddGroup_RingoidSigTerm2 n A)) 
      *OL2 : ((OpAddGroup_RingoidSigTerm2 n A) → ((OpAddGroup_RingoidSigTerm2 n A) → (OpAddGroup_RingoidSigTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClAddGroup_RingoidSigTerm A) → (ClAddGroup_RingoidSigTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (negCl x1) = (negCl (simplifyCl _ x1))  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpAddGroup_RingoidSigTerm n) → (OpAddGroup_RingoidSigTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (negOL x1) = (negOL (simplifyOpB _ x1))  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpAddGroup_RingoidSigTerm2 n A) → (OpAddGroup_RingoidSigTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (negOL2 x1) = (negOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AddGroup_RingoidSig A) → (AddGroup_RingoidSigTerm → A)) 
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))  
  evalB Ad 0L = (0ᵢ Ad)  
  evalB Ad (negL x1) = ((neg Ad) (evalB Ad x1))  
  evalB Ad (*L x1 x2) = ((* Ad) (evalB Ad x1) (evalB Ad x2))  
  evalCl :  {A : Set} →  ((AddGroup_RingoidSig A) → ((ClAddGroup_RingoidSigTerm A) → A)) 
  evalCl Ad (sing x1) = x1  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))  
  evalCl Ad 0Cl = (0ᵢ Ad)  
  evalCl Ad (negCl x1) = ((neg Ad) (evalCl Ad x1))  
  evalCl Ad (*Cl x1 x2) = ((* Ad) (evalCl Ad x1) (evalCl Ad x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((AddGroup_RingoidSig A) → ((Vec A n) → ((OpAddGroup_RingoidSigTerm n) → A))) 
  evalOpB n Ad vars (v x1) = (lookup vars x1)  
  evalOpB n Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB n Ad vars x1) (evalOpB n Ad vars x2))  
  evalOpB n Ad vars 0OL = (0ᵢ Ad)  
  evalOpB n Ad vars (negOL x1) = ((neg Ad) (evalOpB n Ad vars x1))  
  evalOpB n Ad vars (*OL x1 x2) = ((* Ad) (evalOpB n Ad vars x1) (evalOpB n Ad vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((AddGroup_RingoidSig A) → ((Vec A n) → ((OpAddGroup_RingoidSigTerm2 n A) → A))) 
  evalOp n Ad vars (v2 x1) = (lookup vars x1)  
  evalOp n Ad vars (sing2 x1) = x1  
  evalOp n Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp n Ad vars x1) (evalOp n Ad vars x2))  
  evalOp n Ad vars 0OL2 = (0ᵢ Ad)  
  evalOp n Ad vars (negOL2 x1) = ((neg Ad) (evalOp n Ad vars x1))  
  evalOp n Ad vars (*OL2 x1 x2) = ((* Ad) (evalOp n Ad vars x1) (evalOp n Ad vars x2))  
  inductionB :  (P : (AddGroup_RingoidSigTerm → Set)) →  (( (x1 x2 : AddGroup_RingoidSigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : AddGroup_RingoidSigTerm) → ((P x1) → (P (negL x1)))) → (( (x1 x2 : AddGroup_RingoidSigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : AddGroup_RingoidSigTerm) → (P x)))))) 
  inductionB p p+l p0l pnegl p*l (+L x1 x2) = (p+l _ _ (inductionB p p+l p0l pnegl p*l x1) (inductionB p p+l p0l pnegl p*l x2))  
  inductionB p p+l p0l pnegl p*l 0L = p0l  
  inductionB p p+l p0l pnegl p*l (negL x1) = (pnegl _ (inductionB p p+l p0l pnegl p*l x1))  
  inductionB p p+l p0l pnegl p*l (*L x1 x2) = (p*l _ _ (inductionB p p+l p0l pnegl p*l x1) (inductionB p p+l p0l pnegl p*l x2))  
  inductionCl :  (A : Set) (P : ((ClAddGroup_RingoidSigTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAddGroup_RingoidSigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClAddGroup_RingoidSigTerm A)) → ((P x1) → (P (negCl x1)))) → (( (x1 x2 : (ClAddGroup_RingoidSigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClAddGroup_RingoidSigTerm A)) → (P x))))))) 
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl p*cl x1) (inductionCl _ p psing p+cl p0cl pnegcl p*cl x2))  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl 0Cl = p0cl  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (negCl x1) = (pnegcl _ (inductionCl _ p psing p+cl p0cl pnegcl p*cl x1))  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl p*cl x1) (inductionCl _ p psing p+cl p0cl pnegcl p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpAddGroup_RingoidSigTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAddGroup_RingoidSigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpAddGroup_RingoidSigTerm n)) → ((P x1) → (P (negOL x1)))) → (( (x1 x2 : (OpAddGroup_RingoidSigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpAddGroup_RingoidSigTerm n)) → (P x))))))) 
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol p0ol pnegol p*ol x1) (inductionOpB _ p pv p+ol p0ol pnegol p*ol x2))  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol 0OL = p0ol  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (negOL x1) = (pnegol _ (inductionOpB _ p pv p+ol p0ol pnegol p*ol x1))  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p+ol p0ol pnegol p*ol x1) (inductionOpB _ p pv p+ol p0ol pnegol p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpAddGroup_RingoidSigTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAddGroup_RingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpAddGroup_RingoidSigTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → (( (x1 x2 : (OpAddGroup_RingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpAddGroup_RingoidSigTerm2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x2))  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (negOL2 x1) = (pnegol2 _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x1))  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x2))  
  stageB :  (AddGroup_RingoidSigTerm → (Staged AddGroup_RingoidSigTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClAddGroup_RingoidSigTerm A) → (Staged (ClAddGroup_RingoidSigTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl _ x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpAddGroup_RingoidSigTerm n) → (Staged (OpAddGroup_RingoidSigTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB _ x1))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpAddGroup_RingoidSigTerm2 n A) → (Staged (OpAddGroup_RingoidSigTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp _ _ x1))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A)) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 