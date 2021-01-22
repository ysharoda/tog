
module AdditiveSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAdditiveSemigroup  (A : Set) (+ : (A → (A → A))) : Set where 
     field  
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z)))  
  
  record AdditiveSemigroup  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      isAdditiveSemigroup : (IsAdditiveSemigroup A (+))  
  
  open AdditiveSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveSemigroup A1)) (Ad2 : (AdditiveSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveSemigroup A1)) (Ad2 : (AdditiveSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2)))))  
  
  data AdditiveSemigroupTerm   : Set where 
      +L : (AdditiveSemigroupTerm → (AdditiveSemigroupTerm → AdditiveSemigroupTerm))  
      
  data ClAdditiveSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClAdditiveSemigroupTerm A)) 
      +Cl : ((ClAdditiveSemigroupTerm A) → ((ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A)))  
      
  data OpAdditiveSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAdditiveSemigroupTerm n)) 
      +OL : ((OpAdditiveSemigroupTerm n) → ((OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n)))  
      
  data OpAdditiveSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAdditiveSemigroupTerm2 n A)) 
      sing2 : (A → (OpAdditiveSemigroupTerm2 n A)) 
      +OL2 : ((OpAdditiveSemigroupTerm2 n A) → ((OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClAdditiveSemigroupTerm A) → (ClAdditiveSemigroupTerm A)) 
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAdditiveSemigroupTerm n) → (OpAdditiveSemigroupTerm n)) 
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAdditiveSemigroupTerm2 n A) → (OpAdditiveSemigroupTerm2 n A)) 
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AdditiveSemigroup A) → (AdditiveSemigroupTerm → A)) 
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))  
  evalCl :  {A : Set} →  ((AdditiveSemigroup A) → ((ClAdditiveSemigroupTerm A) → A)) 
  evalCl Ad (sing x1) = x1  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((AdditiveSemigroup A) → ((Vec A n) → ((OpAdditiveSemigroupTerm n) → A))) 
  evalOpB Ad vars (v x1) = (lookup vars x1)  
  evalOpB Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((AdditiveSemigroup A) → ((Vec A n) → ((OpAdditiveSemigroupTerm2 n A) → A))) 
  evalOp Ad vars (v2 x1) = (lookup vars x1)  
  evalOp Ad vars (sing2 x1) = x1  
  evalOp Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  inductionB :  {P : (AdditiveSemigroupTerm → Set)} →  (( (x1 x2 : AdditiveSemigroupTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : AdditiveSemigroupTerm) → (P x))) 
  inductionB p+l (+L x1 x2) = (p+l _ _ (inductionB p+l x1) (inductionB p+l x2))  
  inductionCl :  {A : Set} {P : ((ClAdditiveSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAdditiveSemigroupTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClAdditiveSemigroupTerm A)) → (P x)))) 
  inductionCl psing p+cl (sing x1) = (psing x1)  
  inductionCl psing p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p+cl x1) (inductionCl psing p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpAdditiveSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAdditiveSemigroupTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpAdditiveSemigroupTerm n)) → (P x)))) 
  inductionOpB pv p+ol (v x1) = (pv x1)  
  inductionOpB pv p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p+ol x1) (inductionOpB pv p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAdditiveSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAdditiveSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpAdditiveSemigroupTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p+ol2 x1) (inductionOp pv2 psing2 p+ol2 x2))  
  stageB :  (AdditiveSemigroupTerm → (Staged AdditiveSemigroupTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClAdditiveSemigroupTerm A) → (Staged (ClAdditiveSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpAdditiveSemigroupTerm n) → (Staged (OpAdditiveSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpAdditiveSemigroupTerm2 n A) → (Staged (OpAdditiveSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 