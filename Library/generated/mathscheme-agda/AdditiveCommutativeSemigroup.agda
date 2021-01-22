
module AdditiveCommutativeSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveCommutativeSemigroup  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z)))  
  
  open AdditiveCommutativeSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveCommutativeSemigroup A1)) (Ad2 : (AdditiveCommutativeSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveCommutativeSemigroup A1)) (Ad2 : (AdditiveCommutativeSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2)))))  
  
  data AdditiveCommutativeSemigroupTerm   : Set where 
      +L : (AdditiveCommutativeSemigroupTerm → (AdditiveCommutativeSemigroupTerm → AdditiveCommutativeSemigroupTerm))  
      
  data ClAdditiveCommutativeSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClAdditiveCommutativeSemigroupTerm A)) 
      +Cl : ((ClAdditiveCommutativeSemigroupTerm A) → ((ClAdditiveCommutativeSemigroupTerm A) → (ClAdditiveCommutativeSemigroupTerm A)))  
      
  data OpAdditiveCommutativeSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAdditiveCommutativeSemigroupTerm n)) 
      +OL : ((OpAdditiveCommutativeSemigroupTerm n) → ((OpAdditiveCommutativeSemigroupTerm n) → (OpAdditiveCommutativeSemigroupTerm n)))  
      
  data OpAdditiveCommutativeSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAdditiveCommutativeSemigroupTerm2 n A)) 
      sing2 : (A → (OpAdditiveCommutativeSemigroupTerm2 n A)) 
      +OL2 : ((OpAdditiveCommutativeSemigroupTerm2 n A) → ((OpAdditiveCommutativeSemigroupTerm2 n A) → (OpAdditiveCommutativeSemigroupTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClAdditiveCommutativeSemigroupTerm A) → (ClAdditiveCommutativeSemigroupTerm A)) 
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAdditiveCommutativeSemigroupTerm n) → (OpAdditiveCommutativeSemigroupTerm n)) 
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAdditiveCommutativeSemigroupTerm2 n A) → (OpAdditiveCommutativeSemigroupTerm2 n A)) 
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AdditiveCommutativeSemigroup A) → (AdditiveCommutativeSemigroupTerm → A)) 
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))  
  evalCl :  {A : Set} →  ((AdditiveCommutativeSemigroup A) → ((ClAdditiveCommutativeSemigroupTerm A) → A)) 
  evalCl Ad (sing x1) = x1  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((AdditiveCommutativeSemigroup A) → ((Vec A n) → ((OpAdditiveCommutativeSemigroupTerm n) → A))) 
  evalOpB Ad vars (v x1) = (lookup vars x1)  
  evalOpB Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((AdditiveCommutativeSemigroup A) → ((Vec A n) → ((OpAdditiveCommutativeSemigroupTerm2 n A) → A))) 
  evalOp Ad vars (v2 x1) = (lookup vars x1)  
  evalOp Ad vars (sing2 x1) = x1  
  evalOp Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  inductionB :  {P : (AdditiveCommutativeSemigroupTerm → Set)} →  (( (x1 x2 : AdditiveCommutativeSemigroupTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : AdditiveCommutativeSemigroupTerm) → (P x))) 
  inductionB p+l (+L x1 x2) = (p+l _ _ (inductionB p+l x1) (inductionB p+l x2))  
  inductionCl :  {A : Set} {P : ((ClAdditiveCommutativeSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAdditiveCommutativeSemigroupTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClAdditiveCommutativeSemigroupTerm A)) → (P x)))) 
  inductionCl psing p+cl (sing x1) = (psing x1)  
  inductionCl psing p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p+cl x1) (inductionCl psing p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpAdditiveCommutativeSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAdditiveCommutativeSemigroupTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpAdditiveCommutativeSemigroupTerm n)) → (P x)))) 
  inductionOpB pv p+ol (v x1) = (pv x1)  
  inductionOpB pv p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p+ol x1) (inductionOpB pv p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAdditiveCommutativeSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAdditiveCommutativeSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpAdditiveCommutativeSemigroupTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p+ol2 x1) (inductionOp pv2 psing2 p+ol2 x2))  
  stageB :  (AdditiveCommutativeSemigroupTerm → (Staged AdditiveCommutativeSemigroupTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClAdditiveCommutativeSemigroupTerm A) → (Staged (ClAdditiveCommutativeSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpAdditiveCommutativeSemigroupTerm n) → (Staged (OpAdditiveCommutativeSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpAdditiveCommutativeSemigroupTerm2 n A) → (Staged (OpAdditiveCommutativeSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 