
module MultGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultGroup  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      inv : (A → A) 
      leftInverse_inv_op_1ᵢ : ( {x : A} → (* x (inv x)) ≡ 1ᵢ) 
      rightInverse_inv_op_1ᵢ : ( {x : A} → (* (inv x) x) ≡ 1ᵢ)  
  
  open MultGroup
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      1S : AS 
      invS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      invP : ((Prod A A) → (Prod A A)) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftInverse_inv_op_1P : ( {xP : (Prod A A)} → (*P xP (invP xP)) ≡ 1P) 
      rightInverse_inv_op_1P : ( {xP : (Prod A A)} → (*P (invP xP) xP) ≡ 1P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Mu1 : (MultGroup A1)) (Mu2 : (MultGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mu1) x1 x2)) ≡ ((* Mu2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Mu1)) ≡ (1ᵢ Mu2) 
      pres-inv : ( {x1 : A1} → (hom ((inv Mu1) x1)) ≡ ((inv Mu2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mu1 : (MultGroup A1)) (Mu2 : (MultGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mu1) x1 x2) ((* Mu2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Mu1) (1ᵢ Mu2)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Mu1) x1) ((inv Mu2) y1))))  
  
  data MultGroupTerm   : Set where 
      *L : (MultGroupTerm → (MultGroupTerm → MultGroupTerm)) 
      1L : MultGroupTerm 
      invL : (MultGroupTerm → MultGroupTerm)  
      
  data ClMultGroupTerm  (A : Set) : Set where 
      sing : (A → (ClMultGroupTerm A)) 
      *Cl : ((ClMultGroupTerm A) → ((ClMultGroupTerm A) → (ClMultGroupTerm A))) 
      1Cl : (ClMultGroupTerm A) 
      invCl : ((ClMultGroupTerm A) → (ClMultGroupTerm A))  
      
  data OpMultGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMultGroupTerm n)) 
      *OL : ((OpMultGroupTerm n) → ((OpMultGroupTerm n) → (OpMultGroupTerm n))) 
      1OL : (OpMultGroupTerm n) 
      invOL : ((OpMultGroupTerm n) → (OpMultGroupTerm n))  
      
  data OpMultGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMultGroupTerm2 n A)) 
      sing2 : (A → (OpMultGroupTerm2 n A)) 
      *OL2 : ((OpMultGroupTerm2 n A) → ((OpMultGroupTerm2 n A) → (OpMultGroupTerm2 n A))) 
      1OL2 : (OpMultGroupTerm2 n A) 
      invOL2 : ((OpMultGroupTerm2 n A) → (OpMultGroupTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClMultGroupTerm A) → (ClMultGroupTerm A)) 
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpMultGroupTerm n) → (OpMultGroupTerm n)) 
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpMultGroupTerm2 n A) → (OpMultGroupTerm2 n A)) 
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MultGroup A) → (MultGroupTerm → A)) 
  evalB Mu (*L x1 x2) = ((* Mu) (evalB Mu x1) (evalB Mu x2))  
  evalB Mu 1L = (1ᵢ Mu)  
  evalB Mu (invL x1) = ((inv Mu) (evalB Mu x1))  
  evalCl :  {A : Set} →  ((MultGroup A) → ((ClMultGroupTerm A) → A)) 
  evalCl Mu (sing x1) = x1  
  evalCl Mu (*Cl x1 x2) = ((* Mu) (evalCl Mu x1) (evalCl Mu x2))  
  evalCl Mu 1Cl = (1ᵢ Mu)  
  evalCl Mu (invCl x1) = ((inv Mu) (evalCl Mu x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((MultGroup A) → ((Vec A n) → ((OpMultGroupTerm n) → A))) 
  evalOpB Mu vars (v x1) = (lookup vars x1)  
  evalOpB Mu vars (*OL x1 x2) = ((* Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  evalOpB Mu vars 1OL = (1ᵢ Mu)  
  evalOpB Mu vars (invOL x1) = ((inv Mu) (evalOpB Mu vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((MultGroup A) → ((Vec A n) → ((OpMultGroupTerm2 n A) → A))) 
  evalOp Mu vars (v2 x1) = (lookup vars x1)  
  evalOp Mu vars (sing2 x1) = x1  
  evalOp Mu vars (*OL2 x1 x2) = ((* Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  evalOp Mu vars 1OL2 = (1ᵢ Mu)  
  evalOp Mu vars (invOL2 x1) = ((inv Mu) (evalOp Mu vars x1))  
  inductionB :  {P : (MultGroupTerm → Set)} →  (( (x1 x2 : MultGroupTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → (( (x1 : MultGroupTerm) → ((P x1) → (P (invL x1)))) → ( (x : MultGroupTerm) → (P x))))) 
  inductionB p*l p1l pinvl (*L x1 x2) = (p*l _ _ (inductionB p*l p1l pinvl x1) (inductionB p*l p1l pinvl x2))  
  inductionB p*l p1l pinvl 1L = p1l  
  inductionB p*l p1l pinvl (invL x1) = (pinvl _ (inductionB p*l p1l pinvl x1))  
  inductionCl :  {A : Set} {P : ((ClMultGroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMultGroupTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → (( (x1 : (ClMultGroupTerm A)) → ((P x1) → (P (invCl x1)))) → ( (x : (ClMultGroupTerm A)) → (P x)))))) 
  inductionCl psing p*cl p1cl pinvcl (sing x1) = (psing x1)  
  inductionCl psing p*cl p1cl pinvcl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p1cl pinvcl x1) (inductionCl psing p*cl p1cl pinvcl x2))  
  inductionCl psing p*cl p1cl pinvcl 1Cl = p1cl  
  inductionCl psing p*cl p1cl pinvcl (invCl x1) = (pinvcl _ (inductionCl psing p*cl p1cl pinvcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpMultGroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMultGroupTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → (( (x1 : (OpMultGroupTerm n)) → ((P x1) → (P (invOL x1)))) → ( (x : (OpMultGroupTerm n)) → (P x)))))) 
  inductionOpB pv p*ol p1ol pinvol (v x1) = (pv x1)  
  inductionOpB pv p*ol p1ol pinvol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p1ol pinvol x1) (inductionOpB pv p*ol p1ol pinvol x2))  
  inductionOpB pv p*ol p1ol pinvol 1OL = p1ol  
  inductionOpB pv p*ol p1ol pinvol (invOL x1) = (pinvol _ (inductionOpB pv p*ol p1ol pinvol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpMultGroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMultGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → (( (x1 : (OpMultGroupTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → ( (x : (OpMultGroupTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 x1) (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 x2))  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 x1))  
  stageB :  (MultGroupTerm → (Staged MultGroupTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClMultGroupTerm A) → (Staged (ClMultGroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpMultGroupTerm n) → (Staged (OpMultGroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpMultGroupTerm2 n A) → (Staged (OpMultGroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      invT : ((Repr A) → (Repr A))  
  
 