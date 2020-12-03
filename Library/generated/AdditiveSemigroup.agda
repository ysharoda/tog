
 module AdditiveSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveSemigroup (A : Set) : Set where
    constructor AdditiveSemigroupC
    field
      + : A → A → A
      associative_+ : ({x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
  
  open AdditiveSemigroup
  record Sig (AS : Set) : Set where
    constructor SigSigC
    field
      +S : AS → AS → AS 
  
  record Product (A : Set) : Set where
    constructor ProductC
    field
      +P : (Prod A A) → (Prod A A) → (Prod A A)
      associative_+P : ({xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
  
  record Hom {A1 : Set} {A2 : Set} (Ad1 : (AdditiveSemigroup A1)) (Ad2 : (AdditiveSemigroup A2)) : Set where
    constructor HomC
    field
      hom : A1 → A2
      pres-+ : ({x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2))) 
  
  record RelInterp {A1 : Set} {A2 : Set} (Ad1 : (AdditiveSemigroup A1)) (Ad2 : (AdditiveSemigroup A2)) : Set₁ where
    constructor RelInterpC
    field
      interp : A1 → A2 → Set
      interp-+ : ({x1 x2 : A1} {y1 y2 : A2} → (interp x1 y1) → (interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2))) 
  
  data AdditiveSemigroupTerm  : Set where
    +L : AdditiveSemigroupTerm → AdditiveSemigroupTerm → AdditiveSemigroupTerm 
  
  data ClAdditiveSemigroupTerm (A : Set) : Set where
    sing : A → (ClAdditiveSemigroupTerm A)
    +Cl : (ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A) 
  
  data OpAdditiveSemigroupTerm (n : Nat) : Set where
    v : (Fin n) → (OpAdditiveSemigroupTerm n)
    +OL : (OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n) 
  
  data OpAdditiveSemigroupTerm2 (n : Nat) (A : Set) : Set where
    v2 : (Fin n) → (OpAdditiveSemigroupTerm2 n A)
    sing2 : A → (OpAdditiveSemigroupTerm2 n A)
    +OL2 : (OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A) 
  
  simplifyB : AdditiveSemigroupTerm → AdditiveSemigroupTerm
  simplifyB (+L x1 x2) = (+L (simplifyB x1) (simplifyB x2))
  
  simplifyCl : ((A : Set) → (ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A))
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))
  
  simplifyCl _ (sing x1) = (sing x1)
  
  simplifyOpB : ((n : Nat) → (OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n))
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))
  
  simplifyOpB _ (v x1) = (v x1)
  
  simplifyOp : ((n : Nat) (A : Set) → (OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A))
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))
  
  simplifyOp _ _ (v2 x1) = (v2 x1)
  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)
  
  evalB : ({A : Set} → (AdditiveSemigroup A) → AdditiveSemigroupTerm → A)
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))
  
  evalCl : ({A : Set} → (AdditiveSemigroup A) → (ClAdditiveSemigroupTerm A) → A)
  evalCl Ad (sing x1) = x1
  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))
  
  evalOpB : ({A : Set} (n : Nat) → (AdditiveSemigroup A) → (Vec A n) → (OpAdditiveSemigroupTerm n) → A)
  evalOpB n Ad vars (v x1) = (lookup vars x1)
  
  evalOpB n Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB n Ad vars x1) (evalOpB n Ad vars x2))
  
  evalOp : ({A : Set} (n : Nat) → (AdditiveSemigroup A) → (Vec A n) → (OpAdditiveSemigroupTerm2 n A) → A)
  evalOp n Ad vars (v2 x1) = (lookup vars x1)
  
  evalOp n Ad vars (sing2 x1) = x1
  
  evalOp n Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp n Ad vars x1) (evalOp n Ad vars x2))
  
  inductionB : ((P : AdditiveSemigroupTerm → Set) → ((x1 x2 : AdditiveSemigroupTerm) → (P x1) → (P x2) → (P (+L x1 x2))) → ((x : AdditiveSemigroupTerm) → (P x)))
  inductionB p p+l (+L x1 x2) = (p+l _ _ (inductionB p p+l x1) (inductionB p p+l x2))
  
  inductionCl : ((A : Set) (P : (ClAdditiveSemigroupTerm A) → Set) → ((x1 : A) → (P (sing x1))) → ((x1 x2 : (ClAdditiveSemigroupTerm A)) → (P x1) → (P x2) → (P (+Cl x1 x2))) → ((x : (ClAdditiveSemigroupTerm A)) → (P x)))
  inductionCl _ p psing p+cl (sing x1) = (psing x1)
  
  inductionCl _ p psing p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl x1) (inductionCl _ p psing p+cl x2))
  
  inductionOpB : ((n : Nat) (P : (OpAdditiveSemigroupTerm n) → Set) → ((fin : (Fin n)) → (P (v fin))) → ((x1 x2 : (OpAdditiveSemigroupTerm n)) → (P x1) → (P x2) → (P (+OL x1 x2))) → ((x : (OpAdditiveSemigroupTerm n)) → (P x)))
  inductionOpB _ p pv p+ol (v x1) = (pv x1)
  
  inductionOpB _ p pv p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol x1) (inductionOpB _ p pv p+ol x2))
  
  inductionOp : ((n : Nat) (A : Set) (P : (OpAdditiveSemigroupTerm2 n A) → Set) → ((fin : (Fin n)) → (P (v2 fin))) → ((x1 : A) → (P (sing2 x1))) → ((x1 x2 : (OpAdditiveSemigroupTerm2 n A)) → (P x1) → (P x2) → (P (+OL2 x1 x2))) → ((x : (OpAdditiveSemigroupTerm2 n A)) → (P x)))
  inductionOp _ _ p pv2 psing2 p+ol2 (v2 x1) = (pv2 x1)
  
  inductionOp _ _ p pv2 psing2 p+ol2 (sing2 x1) = (psing2 x1)
  
  inductionOp _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 x2))
  
  +L' : ( AdditiveSemigroupTerm → AdditiveSemigroupTerm → AdditiveSemigroupTerm)
  +L' x1 x2 = (+L x1 x2)
  
  stageB : AdditiveSemigroupTerm → (Staged AdditiveSemigroupTerm)
  stageB (+L x1 x2) = (stage2 +L' (codeLift2 +L') (stageB x1) (stageB x2))
  
  +Cl' : ({A : Set} → (ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A))
  +Cl' x1 x2 = (+Cl x1 x2)
  
  stageCl : ((A : Set) → (ClAdditiveSemigroupTerm A) → (Staged (ClAdditiveSemigroupTerm A)))
  stageCl _ (sing x1) = (Now (sing x1))
  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl' (codeLift2 +Cl') ((stageCl _) x1) ((stageCl _) x2))
  
  +OL' : ({n : Nat} → (OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n))
  +OL' x1 x2 = (+OL x1 x2)
  
  stageOpB : ((n : Nat) → (OpAdditiveSemigroupTerm n) → (Staged (OpAdditiveSemigroupTerm n)))
  stageOpB _ (v x1) = (const (code (v x1)))
  
  stageOpB _ (+OL x1 x2) = (stage2 +OL' (codeLift2 +OL') ((stageOpB _) x1) ((stageOpB _) x2))
  
  +OL2' : ({n : Nat} {A : Set} → (OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A))
  +OL2' x1 x2 = (+OL2 x1 x2)
  
  stageOp : ((n : Nat) (A : Set) → (OpAdditiveSemigroupTerm2 n A) → (Staged (OpAdditiveSemigroupTerm2 n A)))
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))
  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))
  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2' (codeLift2 +OL2') ((stageOp _ _) x1) ((stageOp _ _) x2))
  
  record Tagless (A : Set) (Repr : Set → Set) : Set where
    constructor tagless
    field
      +T : (Repr A) → (Repr A) → (Repr A) 
   
