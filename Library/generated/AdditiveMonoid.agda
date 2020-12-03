
 module AdditiveMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveMonoid (A : Set) : Set where
    constructor AdditiveMonoidC
    field
      + : A → A → A
      associative_+ : ({x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z)))
      0ᵢ : A
      lunit_0ᵢ : ({x : A} → (+ 0ᵢ x) ≡ x)
      runit_0ᵢ : ({x : A} → (+ x 0ᵢ) ≡ x) 
  
  open AdditiveMonoid
  record Sig (AS : Set) : Set where
    constructor SigSigC
    field
      +S : AS → AS → AS
      0S : AS 
  
  record Product (A : Set) : Set where
    constructor ProductC
    field
      +P : (Prod A A) → (Prod A A) → (Prod A A)
      0P : (Prod A A)
      associative_+P : ({xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP)))
      lunit_0P : ({xP : (Prod A A)} → (+P 0P xP) ≡ xP)
      runit_0P : ({xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
  
  record Hom {A1 : Set} {A2 : Set} (Ad1 : (AdditiveMonoid A1)) (Ad2 : (AdditiveMonoid A2)) : Set where
    constructor HomC
    field
      hom : A1 → A2
      pres-+ : ({x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2)))
      pres-0 : (hom (0ᵢ Ad1)) ≡ (0ᵢ Ad2) 
  
  record RelInterp {A1 : Set} {A2 : Set} (Ad1 : (AdditiveMonoid A1)) (Ad2 : (AdditiveMonoid A2)) : Set₁ where
    constructor RelInterpC
    field
      interp : A1 → A2 → Set
      interp-+ : ({x1 x2 : A1} {y1 y2 : A2} → (interp x1 y1) → (interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2)))
      interp-0 : (interp (0ᵢ Ad1) (0ᵢ Ad2)) 
  
  data AdditiveMonoidTerm  : Set where
    +L : AdditiveMonoidTerm → AdditiveMonoidTerm → AdditiveMonoidTerm
    0L : AdditiveMonoidTerm 
  
  data ClAdditiveMonoidTerm (A : Set) : Set where
    sing : A → (ClAdditiveMonoidTerm A)
    +Cl : (ClAdditiveMonoidTerm A) → (ClAdditiveMonoidTerm A) → (ClAdditiveMonoidTerm A)
    0Cl : (ClAdditiveMonoidTerm A) 
  
  data OpAdditiveMonoidTerm (n : Nat) : Set where
    v : (Fin n) → (OpAdditiveMonoidTerm n)
    +OL : (OpAdditiveMonoidTerm n) → (OpAdditiveMonoidTerm n) → (OpAdditiveMonoidTerm n)
    0OL : (OpAdditiveMonoidTerm n) 
  
  data OpAdditiveMonoidTerm2 (n : Nat) (A : Set) : Set where
    v2 : (Fin n) → (OpAdditiveMonoidTerm2 n A)
    sing2 : A → (OpAdditiveMonoidTerm2 n A)
    +OL2 : (OpAdditiveMonoidTerm2 n A) → (OpAdditiveMonoidTerm2 n A) → (OpAdditiveMonoidTerm2 n A)
    0OL2 : (OpAdditiveMonoidTerm2 n A) 
  
  simplifyB : AdditiveMonoidTerm → AdditiveMonoidTerm
  simplifyB (+L 0L x) = x
  
  simplifyB (+L x 0L) = x
  
  simplifyB (+L x1 x2) = (+L (simplifyB x1) (simplifyB x2))
  
  simplifyB 0L = 0L
  
  simplifyCl : ((A : Set) → (ClAdditiveMonoidTerm A) → (ClAdditiveMonoidTerm A))
  simplifyCl _ (+Cl 0Cl x) = x
  
  simplifyCl _ (+Cl x 0Cl) = x
  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))
  
  simplifyCl _ 0Cl = 0Cl
  
  simplifyCl _ (sing x1) = (sing x1)
  
  simplifyOpB : ((n : Nat) → (OpAdditiveMonoidTerm n) → (OpAdditiveMonoidTerm n))
  simplifyOpB _ (+OL 0OL x) = x
  
  simplifyOpB _ (+OL x 0OL) = x
  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))
  
  simplifyOpB _ 0OL = 0OL
  
  simplifyOpB _ (v x1) = (v x1)
  
  simplifyOp : ((n : Nat) (A : Set) → (OpAdditiveMonoidTerm2 n A) → (OpAdditiveMonoidTerm2 n A))
  simplifyOp _ _ (+OL2 0OL2 x) = x
  
  simplifyOp _ _ (+OL2 x 0OL2) = x
  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))
  
  simplifyOp _ _ 0OL2 = 0OL2
  
  simplifyOp _ _ (v2 x1) = (v2 x1)
  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)
  
  evalB : ({A : Set} → (AdditiveMonoid A) → AdditiveMonoidTerm → A)
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))
  
  evalB Ad 0L = (0ᵢ Ad)
  
  evalCl : ({A : Set} → (AdditiveMonoid A) → (ClAdditiveMonoidTerm A) → A)
  evalCl Ad (sing x1) = x1
  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))
  
  evalCl Ad 0Cl = (0ᵢ Ad)
  
  evalOpB : ({A : Set} (n : Nat) → (AdditiveMonoid A) → (Vec A n) → (OpAdditiveMonoidTerm n) → A)
  evalOpB n Ad vars (v x1) = (lookup vars x1)
  
  evalOpB n Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB n Ad vars x1) (evalOpB n Ad vars x2))
  
  evalOpB n Ad vars 0OL = (0ᵢ Ad)
  
  evalOp : ({A : Set} (n : Nat) → (AdditiveMonoid A) → (Vec A n) → (OpAdditiveMonoidTerm2 n A) → A)
  evalOp n Ad vars (v2 x1) = (lookup vars x1)
  
  evalOp n Ad vars (sing2 x1) = x1
  
  evalOp n Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp n Ad vars x1) (evalOp n Ad vars x2))
  
  evalOp n Ad vars 0OL2 = (0ᵢ Ad)
  
  inductionB : ((P : AdditiveMonoidTerm → Set) → ((x1 x2 : AdditiveMonoidTerm) → (P x1) → (P x2) → (P (+L x1 x2))) → (P 0L) → ((x : AdditiveMonoidTerm) → (P x)))
  inductionB p p+l p0l (+L x1 x2) = (p+l _ _ (inductionB p p+l p0l x1) (inductionB p p+l p0l x2))
  
  inductionB p p+l p0l 0L = p0l
  
  inductionCl : ((A : Set) (P : (ClAdditiveMonoidTerm A) → Set) → ((x1 : A) → (P (sing x1))) → ((x1 x2 : (ClAdditiveMonoidTerm A)) → (P x1) → (P x2) → (P (+Cl x1 x2))) → (P 0Cl) → ((x : (ClAdditiveMonoidTerm A)) → (P x)))
  inductionCl _ p psing p+cl p0cl (sing x1) = (psing x1)
  
  inductionCl _ p psing p+cl p0cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl p0cl x1) (inductionCl _ p psing p+cl p0cl x2))
  
  inductionCl _ p psing p+cl p0cl 0Cl = p0cl
  
  inductionOpB : ((n : Nat) (P : (OpAdditiveMonoidTerm n) → Set) → ((fin : (Fin n)) → (P (v fin))) → ((x1 x2 : (OpAdditiveMonoidTerm n)) → (P x1) → (P x2) → (P (+OL x1 x2))) → (P 0OL) → ((x : (OpAdditiveMonoidTerm n)) → (P x)))
  inductionOpB _ p pv p+ol p0ol (v x1) = (pv x1)
  
  inductionOpB _ p pv p+ol p0ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol p0ol x1) (inductionOpB _ p pv p+ol p0ol x2))
  
  inductionOpB _ p pv p+ol p0ol 0OL = p0ol
  
  inductionOp : ((n : Nat) (A : Set) (P : (OpAdditiveMonoidTerm2 n A) → Set) → ((fin : (Fin n)) → (P (v2 fin))) → ((x1 : A) → (P (sing2 x1))) → ((x1 x2 : (OpAdditiveMonoidTerm2 n A)) → (P x1) → (P x2) → (P (+OL2 x1 x2))) → (P 0OL2) → ((x : (OpAdditiveMonoidTerm2 n A)) → (P x)))
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 (v2 x1) = (pv2 x1)
  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 (sing2 x1) = (psing2 x1)
  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 x2))
  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 0OL2 = p0ol2
  
  +L' : ( AdditiveMonoidTerm → AdditiveMonoidTerm → AdditiveMonoidTerm)
  +L' x1 x2 = (+L x1 x2)
  
  0L' : ( AdditiveMonoidTerm)
  0L'  = 0L
  
  stageB : AdditiveMonoidTerm → (Staged AdditiveMonoidTerm)
  stageB (+L x1 x2) = (stage2 +L' (codeLift2 +L') (stageB x1) (stageB x2))
  
  stageB 0L = (Now 0L)
  
  +Cl' : ({A : Set} → (ClAdditiveMonoidTerm A) → (ClAdditiveMonoidTerm A) → (ClAdditiveMonoidTerm A))
  +Cl' x1 x2 = (+Cl x1 x2)
  
  0Cl' : ({A : Set} → (ClAdditiveMonoidTerm A))
  0Cl'  = 0Cl
  
  stageCl : ((A : Set) → (ClAdditiveMonoidTerm A) → (Staged (ClAdditiveMonoidTerm A)))
  stageCl _ (sing x1) = (Now (sing x1))
  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl' (codeLift2 +Cl') ((stageCl _) x1) ((stageCl _) x2))
  
  stageCl _ 0Cl = (Now 0Cl)
  
  +OL' : ({n : Nat} → (OpAdditiveMonoidTerm n) → (OpAdditiveMonoidTerm n) → (OpAdditiveMonoidTerm n))
  +OL' x1 x2 = (+OL x1 x2)
  
  0OL' : ({n : Nat} → (OpAdditiveMonoidTerm n))
  0OL'  = 0OL
  
  stageOpB : ((n : Nat) → (OpAdditiveMonoidTerm n) → (Staged (OpAdditiveMonoidTerm n)))
  stageOpB _ (v x1) = (const (code (v x1)))
  
  stageOpB _ (+OL x1 x2) = (stage2 +OL' (codeLift2 +OL') ((stageOpB _) x1) ((stageOpB _) x2))
  
  stageOpB _ 0OL = (Now 0OL)
  
  +OL2' : ({n : Nat} {A : Set} → (OpAdditiveMonoidTerm2 n A) → (OpAdditiveMonoidTerm2 n A) → (OpAdditiveMonoidTerm2 n A))
  +OL2' x1 x2 = (+OL2 x1 x2)
  
  0OL2' : ({n : Nat} {A : Set} → (OpAdditiveMonoidTerm2 n A))
  0OL2'  = 0OL2
  
  stageOp : ((n : Nat) (A : Set) → (OpAdditiveMonoidTerm2 n A) → (Staged (OpAdditiveMonoidTerm2 n A)))
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))
  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))
  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2' (codeLift2 +OL2') ((stageOp _ _) x1) ((stageOp _ _) x2))
  
  stageOp _ _ 0OL2 = (Now 0OL2)
  
  record Tagless (A : Set) (Repr : Set → Set) : Set where
    constructor tagless
    field
      +T : (Repr A) → (Repr A) → (Repr A)
      0T : (Repr A) 
   
