
module AbelianGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAbelianGroup  (A : Set) (1ᵢ : A) (* : (A → (A → A))) (inv : (A → A)) : Set where 
     field  
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftInverse_inv_op_1ᵢ : ( {x : A} → (* x (inv x)) ≡ 1ᵢ) 
      rightInverse_inv_op_1ᵢ : ( {x : A} → (* (inv x) x) ≡ 1ᵢ) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x))  
  
  record AbelianGroup  (A : Set) : Set where 
     field  
      1ᵢ : A 
      * : (A → (A → A)) 
      inv : (A → A) 
      isAbelianGroup : (IsAbelianGroup A 1ᵢ (*) inv)  
  
  open AbelianGroup
  record Sig  (AS : Set) : Set where 
     field  
      1S : AS 
      *S : (AS → (AS → AS)) 
      invS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      1P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      invP : ((Prod A A) → (Prod A A)) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftInverse_inv_op_1P : ( {xP : (Prod A A)} → (*P xP (invP xP)) ≡ 1P) 
      rightInverse_inv_op_1P : ( {xP : (Prod A A)} → (*P (invP xP) xP) ≡ 1P) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ab1 : (AbelianGroup A1)) (Ab2 : (AbelianGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-1 : (hom (1ᵢ Ab1)) ≡ (1ᵢ Ab2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ab1) x1 x2)) ≡ ((* Ab2) (hom x1) (hom x2))) 
      pres-inv : ( {x1 : A1} → (hom ((inv Ab1) x1)) ≡ ((inv Ab2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ab1 : (AbelianGroup A1)) (Ab2 : (AbelianGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-1 : (interp (1ᵢ Ab1) (1ᵢ Ab2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ab1) x1 x2) ((* Ab2) y1 y2))))) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Ab1) x1) ((inv Ab2) y1))))  
  
  data AbelianGroupTerm   : Set where 
      1L : AbelianGroupTerm 
      *L : (AbelianGroupTerm → (AbelianGroupTerm → AbelianGroupTerm)) 
      invL : (AbelianGroupTerm → AbelianGroupTerm)  
      
  data ClAbelianGroupTerm  (A : Set) : Set where 
      sing : (A → (ClAbelianGroupTerm A)) 
      1Cl : (ClAbelianGroupTerm A) 
      *Cl : ((ClAbelianGroupTerm A) → ((ClAbelianGroupTerm A) → (ClAbelianGroupTerm A))) 
      invCl : ((ClAbelianGroupTerm A) → (ClAbelianGroupTerm A))  
      
  data OpAbelianGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAbelianGroupTerm n)) 
      1OL : (OpAbelianGroupTerm n) 
      *OL : ((OpAbelianGroupTerm n) → ((OpAbelianGroupTerm n) → (OpAbelianGroupTerm n))) 
      invOL : ((OpAbelianGroupTerm n) → (OpAbelianGroupTerm n))  
      
  data OpAbelianGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAbelianGroupTerm2 n A)) 
      sing2 : (A → (OpAbelianGroupTerm2 n A)) 
      1OL2 : (OpAbelianGroupTerm2 n A) 
      *OL2 : ((OpAbelianGroupTerm2 n A) → ((OpAbelianGroupTerm2 n A) → (OpAbelianGroupTerm2 n A))) 
      invOL2 : ((OpAbelianGroupTerm2 n A) → (OpAbelianGroupTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClAbelianGroupTerm A) → (ClAbelianGroupTerm A)) 
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAbelianGroupTerm n) → (OpAbelianGroupTerm n)) 
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAbelianGroupTerm2 n A) → (OpAbelianGroupTerm2 n A)) 
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AbelianGroup A) → (AbelianGroupTerm → A)) 
  evalB Ab 1L = (1ᵢ Ab)  
  evalB Ab (*L x1 x2) = ((* Ab) (evalB Ab x1) (evalB Ab x2))  
  evalB Ab (invL x1) = ((inv Ab) (evalB Ab x1))  
  evalCl :  {A : Set} →  ((AbelianGroup A) → ((ClAbelianGroupTerm A) → A)) 
  evalCl Ab (sing x1) = x1  
  evalCl Ab 1Cl = (1ᵢ Ab)  
  evalCl Ab (*Cl x1 x2) = ((* Ab) (evalCl Ab x1) (evalCl Ab x2))  
  evalCl Ab (invCl x1) = ((inv Ab) (evalCl Ab x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((AbelianGroup A) → ((Vec A n) → ((OpAbelianGroupTerm n) → A))) 
  evalOpB Ab vars (v x1) = (lookup vars x1)  
  evalOpB Ab vars 1OL = (1ᵢ Ab)  
  evalOpB Ab vars (*OL x1 x2) = ((* Ab) (evalOpB Ab vars x1) (evalOpB Ab vars x2))  
  evalOpB Ab vars (invOL x1) = ((inv Ab) (evalOpB Ab vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((AbelianGroup A) → ((Vec A n) → ((OpAbelianGroupTerm2 n A) → A))) 
  evalOp Ab vars (v2 x1) = (lookup vars x1)  
  evalOp Ab vars (sing2 x1) = x1  
  evalOp Ab vars 1OL2 = (1ᵢ Ab)  
  evalOp Ab vars (*OL2 x1 x2) = ((* Ab) (evalOp Ab vars x1) (evalOp Ab vars x2))  
  evalOp Ab vars (invOL2 x1) = ((inv Ab) (evalOp Ab vars x1))  
  inductionB :  {P : (AbelianGroupTerm → Set)} →  ((P 1L) → (( (x1 x2 : AbelianGroupTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 : AbelianGroupTerm) → ((P x1) → (P (invL x1)))) → ( (x : AbelianGroupTerm) → (P x))))) 
  inductionB p1l p*l pinvl 1L = p1l  
  inductionB p1l p*l pinvl (*L x1 x2) = (p*l _ _ (inductionB p1l p*l pinvl x1) (inductionB p1l p*l pinvl x2))  
  inductionB p1l p*l pinvl (invL x1) = (pinvl _ (inductionB p1l p*l pinvl x1))  
  inductionCl :  {A : Set} {P : ((ClAbelianGroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 1Cl) → (( (x1 x2 : (ClAbelianGroupTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 : (ClAbelianGroupTerm A)) → ((P x1) → (P (invCl x1)))) → ( (x : (ClAbelianGroupTerm A)) → (P x)))))) 
  inductionCl psing p1cl p*cl pinvcl (sing x1) = (psing x1)  
  inductionCl psing p1cl p*cl pinvcl 1Cl = p1cl  
  inductionCl psing p1cl p*cl pinvcl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p1cl p*cl pinvcl x1) (inductionCl psing p1cl p*cl pinvcl x2))  
  inductionCl psing p1cl p*cl pinvcl (invCl x1) = (pinvcl _ (inductionCl psing p1cl p*cl pinvcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpAbelianGroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 1OL) → (( (x1 x2 : (OpAbelianGroupTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 : (OpAbelianGroupTerm n)) → ((P x1) → (P (invOL x1)))) → ( (x : (OpAbelianGroupTerm n)) → (P x)))))) 
  inductionOpB pv p1ol p*ol pinvol (v x1) = (pv x1)  
  inductionOpB pv p1ol p*ol pinvol 1OL = p1ol  
  inductionOpB pv p1ol p*ol pinvol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p1ol p*ol pinvol x1) (inductionOpB pv p1ol p*ol pinvol x2))  
  inductionOpB pv p1ol p*ol pinvol (invOL x1) = (pinvol _ (inductionOpB pv p1ol p*ol pinvol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAbelianGroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 1OL2) → (( (x1 x2 : (OpAbelianGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 : (OpAbelianGroupTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → ( (x : (OpAbelianGroupTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 x1) (inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 x2))  
  inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 p1ol2 p*ol2 pinvol2 x1))  
  stageB :  (AbelianGroupTerm → (Staged AbelianGroupTerm))
  stageB 1L = (Now 1L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClAbelianGroupTerm A) → (Staged (ClAbelianGroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpAbelianGroupTerm n) → (Staged (OpAbelianGroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpAbelianGroupTerm2 n A) → (Staged (OpAbelianGroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      1T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      invT : ((Repr A) → (Repr A))  
  
 