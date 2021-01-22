
module AdditiveUnaryAntiDistribution   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAdditiveUnaryAntiDistribution  (A : Set) (prim : (A → A)) (+ : (A → (A → A))) : Set where 
     field  
      antidis_prim_+ : ( {x y : A} → (prim (+ x y)) ≡ (+ (prim y) (prim x)))  
  
  record AdditiveUnaryAntiDistribution  (A : Set) : Set where 
     field  
      prim : (A → A) 
      + : (A → (A → A)) 
      isAdditiveUnaryAntiDistribution : (IsAdditiveUnaryAntiDistribution A prim (+))  
  
  open AdditiveUnaryAntiDistribution
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      antidis_prim_+P : ( {xP yP : (Prod A A)} → (primP (+P xP yP)) ≡ (+P (primP yP) (primP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveUnaryAntiDistribution A1)) (Ad2 : (AdditiveUnaryAntiDistribution A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim Ad1) x1)) ≡ ((prim Ad2) (hom x1))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ad1) x1 x2)) ≡ ((+ Ad2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ad1 : (AdditiveUnaryAntiDistribution A1)) (Ad2 : (AdditiveUnaryAntiDistribution A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Ad1) x1) ((prim Ad2) y1)))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ad1) x1 x2) ((+ Ad2) y1 y2)))))  
  
  data AdditiveUnaryAntiDistributionTerm   : Set where 
      primL : (AdditiveUnaryAntiDistributionTerm → AdditiveUnaryAntiDistributionTerm) 
      +L : (AdditiveUnaryAntiDistributionTerm → (AdditiveUnaryAntiDistributionTerm → AdditiveUnaryAntiDistributionTerm))  
      
  data ClAdditiveUnaryAntiDistributionTerm  (A : Set) : Set where 
      sing : (A → (ClAdditiveUnaryAntiDistributionTerm A)) 
      primCl : ((ClAdditiveUnaryAntiDistributionTerm A) → (ClAdditiveUnaryAntiDistributionTerm A)) 
      +Cl : ((ClAdditiveUnaryAntiDistributionTerm A) → ((ClAdditiveUnaryAntiDistributionTerm A) → (ClAdditiveUnaryAntiDistributionTerm A)))  
      
  data OpAdditiveUnaryAntiDistributionTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAdditiveUnaryAntiDistributionTerm n)) 
      primOL : ((OpAdditiveUnaryAntiDistributionTerm n) → (OpAdditiveUnaryAntiDistributionTerm n)) 
      +OL : ((OpAdditiveUnaryAntiDistributionTerm n) → ((OpAdditiveUnaryAntiDistributionTerm n) → (OpAdditiveUnaryAntiDistributionTerm n)))  
      
  data OpAdditiveUnaryAntiDistributionTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAdditiveUnaryAntiDistributionTerm2 n A)) 
      sing2 : (A → (OpAdditiveUnaryAntiDistributionTerm2 n A)) 
      primOL2 : ((OpAdditiveUnaryAntiDistributionTerm2 n A) → (OpAdditiveUnaryAntiDistributionTerm2 n A)) 
      +OL2 : ((OpAdditiveUnaryAntiDistributionTerm2 n A) → ((OpAdditiveUnaryAntiDistributionTerm2 n A) → (OpAdditiveUnaryAntiDistributionTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClAdditiveUnaryAntiDistributionTerm A) → (ClAdditiveUnaryAntiDistributionTerm A)) 
  simplifyCl (+Cl (primCl y) (primCl x)) = (primCl (+Cl x y))  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAdditiveUnaryAntiDistributionTerm n) → (OpAdditiveUnaryAntiDistributionTerm n)) 
  simplifyOpB (+OL (primOL y) (primOL x)) = (primOL (+OL x y))  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAdditiveUnaryAntiDistributionTerm2 n A) → (OpAdditiveUnaryAntiDistributionTerm2 n A)) 
  simplifyOp (+OL2 (primOL2 y) (primOL2 x)) = (primOL2 (+OL2 x y))  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AdditiveUnaryAntiDistribution A) → (AdditiveUnaryAntiDistributionTerm → A)) 
  evalB Ad (primL x1) = ((prim Ad) (evalB Ad x1))  
  evalB Ad (+L x1 x2) = ((+ Ad) (evalB Ad x1) (evalB Ad x2))  
  evalCl :  {A : Set} →  ((AdditiveUnaryAntiDistribution A) → ((ClAdditiveUnaryAntiDistributionTerm A) → A)) 
  evalCl Ad (sing x1) = x1  
  evalCl Ad (primCl x1) = ((prim Ad) (evalCl Ad x1))  
  evalCl Ad (+Cl x1 x2) = ((+ Ad) (evalCl Ad x1) (evalCl Ad x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((AdditiveUnaryAntiDistribution A) → ((Vec A n) → ((OpAdditiveUnaryAntiDistributionTerm n) → A))) 
  evalOpB Ad vars (v x1) = (lookup vars x1)  
  evalOpB Ad vars (primOL x1) = ((prim Ad) (evalOpB Ad vars x1))  
  evalOpB Ad vars (+OL x1 x2) = ((+ Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((AdditiveUnaryAntiDistribution A) → ((Vec A n) → ((OpAdditiveUnaryAntiDistributionTerm2 n A) → A))) 
  evalOp Ad vars (v2 x1) = (lookup vars x1)  
  evalOp Ad vars (sing2 x1) = x1  
  evalOp Ad vars (primOL2 x1) = ((prim Ad) (evalOp Ad vars x1))  
  evalOp Ad vars (+OL2 x1 x2) = ((+ Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  inductionB :  {P : (AdditiveUnaryAntiDistributionTerm → Set)} →  (( (x1 : AdditiveUnaryAntiDistributionTerm) → ((P x1) → (P (primL x1)))) → (( (x1 x2 : AdditiveUnaryAntiDistributionTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : AdditiveUnaryAntiDistributionTerm) → (P x)))) 
  inductionB ppriml p+l (primL x1) = (ppriml _ (inductionB ppriml p+l x1))  
  inductionB ppriml p+l (+L x1 x2) = (p+l _ _ (inductionB ppriml p+l x1) (inductionB ppriml p+l x2))  
  inductionCl :  {A : Set} {P : ((ClAdditiveUnaryAntiDistributionTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClAdditiveUnaryAntiDistributionTerm A)) → ((P x1) → (P (primCl x1)))) → (( (x1 x2 : (ClAdditiveUnaryAntiDistributionTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClAdditiveUnaryAntiDistributionTerm A)) → (P x))))) 
  inductionCl psing pprimcl p+cl (sing x1) = (psing x1)  
  inductionCl psing pprimcl p+cl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl p+cl x1))  
  inductionCl psing pprimcl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing pprimcl p+cl x1) (inductionCl psing pprimcl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpAdditiveUnaryAntiDistributionTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpAdditiveUnaryAntiDistributionTerm n)) → ((P x1) → (P (primOL x1)))) → (( (x1 x2 : (OpAdditiveUnaryAntiDistributionTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpAdditiveUnaryAntiDistributionTerm n)) → (P x))))) 
  inductionOpB pv pprimol p+ol (v x1) = (pv x1)  
  inductionOpB pv pprimol p+ol (primOL x1) = (pprimol _ (inductionOpB pv pprimol p+ol x1))  
  inductionOpB pv pprimol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv pprimol p+ol x1) (inductionOpB pv pprimol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAdditiveUnaryAntiDistributionTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpAdditiveUnaryAntiDistributionTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → (( (x1 x2 : (OpAdditiveUnaryAntiDistributionTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpAdditiveUnaryAntiDistributionTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 pprimol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 p+ol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 p+ol2 x1))  
  inductionOp pv2 psing2 pprimol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 pprimol2 p+ol2 x1) (inductionOp pv2 psing2 pprimol2 p+ol2 x2))  
  stageB :  (AdditiveUnaryAntiDistributionTerm → (Staged AdditiveUnaryAntiDistributionTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClAdditiveUnaryAntiDistributionTerm A) → (Staged (ClAdditiveUnaryAntiDistributionTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpAdditiveUnaryAntiDistributionTerm n) → (Staged (OpAdditiveUnaryAntiDistributionTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpAdditiveUnaryAntiDistributionTerm2 n A) → (Staged (OpAdditiveUnaryAntiDistributionTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 