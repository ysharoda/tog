
module AdditiveUnital   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveUnital  (A : Set) : Set where 
     field  
      0ᵢ : A 
      + : (A → (A → A)) 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x)  
  
  open AdditiveUnital
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveUnital A1)) (Ad2 : (AdditiveUnital A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Ad1)) ≡ (0ᵢ Ad2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveUnital A1)) (Ad2 : (AdditiveUnital A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Ad1) (0ᵢ Ad2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2)))))  
  
  data AdditiveUnitalTerm   : Set where 
      0L : AdditiveUnitalTerm 
      +L : (AdditiveUnitalTerm → (AdditiveUnitalTerm → AdditiveUnitalTerm))  
      
  data ClAdditiveUnitalTerm  (A : Set) : Set where 
      sing : (A → (ClAdditiveUnitalTerm A)) 
      0Cl : (ClAdditiveUnitalTerm A) 
      +Cl : ((ClAdditiveUnitalTerm A) → ((ClAdditiveUnitalTerm A) → (ClAdditiveUnitalTerm A)))  
      
  data OpAdditiveUnitalTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAdditiveUnitalTerm n)) 
      0OL : (OpAdditiveUnitalTerm n) 
      +OL : ((OpAdditiveUnitalTerm n) → ((OpAdditiveUnitalTerm n) → (OpAdditiveUnitalTerm n)))  
      
  data OpAdditiveUnitalTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAdditiveUnitalTerm2 n A)) 
      sing2 : (A → (OpAdditiveUnitalTerm2 n A)) 
      0OL2 : (OpAdditiveUnitalTerm2 n A) 
      +OL2 : ((OpAdditiveUnitalTerm2 n A) → ((OpAdditiveUnitalTerm2 n A) → (OpAdditiveUnitalTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClAdditiveUnitalTerm A) → (ClAdditiveUnitalTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpAdditiveUnitalTerm n) → (OpAdditiveUnitalTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpAdditiveUnitalTerm2 n A) → (OpAdditiveUnitalTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AdditiveUnital A) → (AdditiveUnitalTerm → A)) 
  evalB Ad 0L = (0ᵢ Ad)  
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))  
  evalCl :  {A : Set} →  ((AdditiveUnital A) → ((ClAdditiveUnitalTerm A) → A)) 
  evalCl Ad (sing x1) = x1  
  evalCl Ad 0Cl = (0ᵢ Ad)  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((AdditiveUnital A) → ((Vec A n) → ((OpAdditiveUnitalTerm n) → A))) 
  evalOpB n Ad vars (v x1) = (lookup vars x1)  
  evalOpB n Ad vars 0OL = (0ᵢ Ad)  
  evalOpB n Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB n Ad vars x1) (evalOpB n Ad vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((AdditiveUnital A) → ((Vec A n) → ((OpAdditiveUnitalTerm2 n A) → A))) 
  evalOp n Ad vars (v2 x1) = (lookup vars x1)  
  evalOp n Ad vars (sing2 x1) = x1  
  evalOp n Ad vars 0OL2 = (0ᵢ Ad)  
  evalOp n Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp n Ad vars x1) (evalOp n Ad vars x2))  
  inductionB :  (P : (AdditiveUnitalTerm → Set)) →  ((P 0L) → (( (x1 x2 : AdditiveUnitalTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : AdditiveUnitalTerm) → (P x)))) 
  inductionB p p0l p+l 0L = p0l  
  inductionB p p0l p+l (+L x1 x2) = (p+l _ _ (inductionB p p0l p+l x1) (inductionB p p0l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClAdditiveUnitalTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClAdditiveUnitalTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClAdditiveUnitalTerm A)) → (P x))))) 
  inductionCl _ p psing p0cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p0cl p+cl 0Cl = p0cl  
  inductionCl _ p psing p0cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p0cl p+cl x1) (inductionCl _ p psing p0cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpAdditiveUnitalTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpAdditiveUnitalTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpAdditiveUnitalTerm n)) → (P x))))) 
  inductionOpB _ p pv p0ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p0ol p+ol 0OL = p0ol  
  inductionOpB _ p pv p0ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p0ol p+ol x1) (inductionOpB _ p pv p0ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpAdditiveUnitalTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpAdditiveUnitalTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpAdditiveUnitalTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 x2))  
  stageB :  (AdditiveUnitalTerm → (Staged AdditiveUnitalTerm))
  stageB 0L = (Now 0L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClAdditiveUnitalTerm A) → (Staged (ClAdditiveUnitalTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpAdditiveUnitalTerm n) → (Staged (OpAdditiveUnitalTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpAdditiveUnitalTerm2 n A) → (Staged (OpAdditiveUnitalTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 