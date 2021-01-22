
module NonassociativeNondistributiveRing   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsNonassociativeNondistributiveRing  (A : Set) (* : (A → (A → A))) (1ᵢ : A) (inv : (A → A)) (+ : (A → (A → A))) : Set where 
     field  
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftInverse_inv_op_1ᵢ : ( {x : A} → (* x (inv x)) ≡ 1ᵢ) 
      rightInverse_inv_op_1ᵢ : ( {x : A} → (* (inv x) x) ≡ 1ᵢ) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x))  
  
  record NonassociativeNondistributiveRing  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      1ᵢ : A 
      inv : (A → A) 
      + : (A → (A → A)) 
      isNonassociativeNondistributiveRing : (IsNonassociativeNondistributiveRing A (*) 1ᵢ inv (+))  
  
  open NonassociativeNondistributiveRing
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      1S : AS 
      invS : (AS → AS) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      invP : ((Prod A A) → (Prod A A)) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftInverse_inv_op_1P : ( {xP : (Prod A A)} → (*P xP (invP xP)) ≡ 1P) 
      rightInverse_inv_op_1P : ( {xP : (Prod A A)} → (*P (invP xP) xP) ≡ 1P) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (No1 : (NonassociativeNondistributiveRing A1)) (No2 : (NonassociativeNondistributiveRing A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* No1) x1 x2)) ≡ ((* No2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ No1)) ≡ (1ᵢ No2) 
      pres-inv : ( {x1 : A1} → (hom ((inv No1) x1)) ≡ ((inv No2) (hom x1))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ No1) x1 x2)) ≡ ((+ No2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (No1 : (NonassociativeNondistributiveRing A1)) (No2 : (NonassociativeNondistributiveRing A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* No1) x1 x2) ((* No2) y1 y2))))) 
      interp-1 : (interp (1ᵢ No1) (1ᵢ No2)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv No1) x1) ((inv No2) y1)))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ No1) x1 x2) ((+ No2) y1 y2)))))  
  
  data NonassociativeNondistributiveRingTerm   : Set where 
      *L : (NonassociativeNondistributiveRingTerm → (NonassociativeNondistributiveRingTerm → NonassociativeNondistributiveRingTerm)) 
      1L : NonassociativeNondistributiveRingTerm 
      invL : (NonassociativeNondistributiveRingTerm → NonassociativeNondistributiveRingTerm) 
      +L : (NonassociativeNondistributiveRingTerm → (NonassociativeNondistributiveRingTerm → NonassociativeNondistributiveRingTerm))  
      
  data ClNonassociativeNondistributiveRingTerm  (A : Set) : Set where 
      sing : (A → (ClNonassociativeNondistributiveRingTerm A)) 
      *Cl : ((ClNonassociativeNondistributiveRingTerm A) → ((ClNonassociativeNondistributiveRingTerm A) → (ClNonassociativeNondistributiveRingTerm A))) 
      1Cl : (ClNonassociativeNondistributiveRingTerm A) 
      invCl : ((ClNonassociativeNondistributiveRingTerm A) → (ClNonassociativeNondistributiveRingTerm A)) 
      +Cl : ((ClNonassociativeNondistributiveRingTerm A) → ((ClNonassociativeNondistributiveRingTerm A) → (ClNonassociativeNondistributiveRingTerm A)))  
      
  data OpNonassociativeNondistributiveRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpNonassociativeNondistributiveRingTerm n)) 
      *OL : ((OpNonassociativeNondistributiveRingTerm n) → ((OpNonassociativeNondistributiveRingTerm n) → (OpNonassociativeNondistributiveRingTerm n))) 
      1OL : (OpNonassociativeNondistributiveRingTerm n) 
      invOL : ((OpNonassociativeNondistributiveRingTerm n) → (OpNonassociativeNondistributiveRingTerm n)) 
      +OL : ((OpNonassociativeNondistributiveRingTerm n) → ((OpNonassociativeNondistributiveRingTerm n) → (OpNonassociativeNondistributiveRingTerm n)))  
      
  data OpNonassociativeNondistributiveRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpNonassociativeNondistributiveRingTerm2 n A)) 
      sing2 : (A → (OpNonassociativeNondistributiveRingTerm2 n A)) 
      *OL2 : ((OpNonassociativeNondistributiveRingTerm2 n A) → ((OpNonassociativeNondistributiveRingTerm2 n A) → (OpNonassociativeNondistributiveRingTerm2 n A))) 
      1OL2 : (OpNonassociativeNondistributiveRingTerm2 n A) 
      invOL2 : ((OpNonassociativeNondistributiveRingTerm2 n A) → (OpNonassociativeNondistributiveRingTerm2 n A)) 
      +OL2 : ((OpNonassociativeNondistributiveRingTerm2 n A) → ((OpNonassociativeNondistributiveRingTerm2 n A) → (OpNonassociativeNondistributiveRingTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClNonassociativeNondistributiveRingTerm A) → (ClNonassociativeNondistributiveRingTerm A)) 
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpNonassociativeNondistributiveRingTerm n) → (OpNonassociativeNondistributiveRingTerm n)) 
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpNonassociativeNondistributiveRingTerm2 n A) → (OpNonassociativeNondistributiveRingTerm2 n A)) 
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((NonassociativeNondistributiveRing A) → (NonassociativeNondistributiveRingTerm → A)) 
  evalB No (*L x1 x2) = ((* No) (evalB No x1) (evalB No x2))  
  evalB No 1L = (1ᵢ No)  
  evalB No (invL x1) = ((inv No) (evalB No x1))  
  evalB No (+L x1 x2) = ((+ No) (evalB No x1) (evalB No x2))  
  evalCl :  {A : Set} →  ((NonassociativeNondistributiveRing A) → ((ClNonassociativeNondistributiveRingTerm A) → A)) 
  evalCl No (sing x1) = x1  
  evalCl No (*Cl x1 x2) = ((* No) (evalCl No x1) (evalCl No x2))  
  evalCl No 1Cl = (1ᵢ No)  
  evalCl No (invCl x1) = ((inv No) (evalCl No x1))  
  evalCl No (+Cl x1 x2) = ((+ No) (evalCl No x1) (evalCl No x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((NonassociativeNondistributiveRing A) → ((Vec A n) → ((OpNonassociativeNondistributiveRingTerm n) → A))) 
  evalOpB No vars (v x1) = (lookup vars x1)  
  evalOpB No vars (*OL x1 x2) = ((* No) (evalOpB No vars x1) (evalOpB No vars x2))  
  evalOpB No vars 1OL = (1ᵢ No)  
  evalOpB No vars (invOL x1) = ((inv No) (evalOpB No vars x1))  
  evalOpB No vars (+OL x1 x2) = ((+ No) (evalOpB No vars x1) (evalOpB No vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((NonassociativeNondistributiveRing A) → ((Vec A n) → ((OpNonassociativeNondistributiveRingTerm2 n A) → A))) 
  evalOp No vars (v2 x1) = (lookup vars x1)  
  evalOp No vars (sing2 x1) = x1  
  evalOp No vars (*OL2 x1 x2) = ((* No) (evalOp No vars x1) (evalOp No vars x2))  
  evalOp No vars 1OL2 = (1ᵢ No)  
  evalOp No vars (invOL2 x1) = ((inv No) (evalOp No vars x1))  
  evalOp No vars (+OL2 x1 x2) = ((+ No) (evalOp No vars x1) (evalOp No vars x2))  
  inductionB :  {P : (NonassociativeNondistributiveRingTerm → Set)} →  (( (x1 x2 : NonassociativeNondistributiveRingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → (( (x1 : NonassociativeNondistributiveRingTerm) → ((P x1) → (P (invL x1)))) → (( (x1 x2 : NonassociativeNondistributiveRingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : NonassociativeNondistributiveRingTerm) → (P x)))))) 
  inductionB p*l p1l pinvl p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p1l pinvl p+l x1) (inductionB p*l p1l pinvl p+l x2))  
  inductionB p*l p1l pinvl p+l 1L = p1l  
  inductionB p*l p1l pinvl p+l (invL x1) = (pinvl _ (inductionB p*l p1l pinvl p+l x1))  
  inductionB p*l p1l pinvl p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p1l pinvl p+l x1) (inductionB p*l p1l pinvl p+l x2))  
  inductionCl :  {A : Set} {P : ((ClNonassociativeNondistributiveRingTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClNonassociativeNondistributiveRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → (( (x1 : (ClNonassociativeNondistributiveRingTerm A)) → ((P x1) → (P (invCl x1)))) → (( (x1 x2 : (ClNonassociativeNondistributiveRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClNonassociativeNondistributiveRingTerm A)) → (P x))))))) 
  inductionCl psing p*cl p1cl pinvcl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p1cl pinvcl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p1cl pinvcl p+cl x1) (inductionCl psing p*cl p1cl pinvcl p+cl x2))  
  inductionCl psing p*cl p1cl pinvcl p+cl 1Cl = p1cl  
  inductionCl psing p*cl p1cl pinvcl p+cl (invCl x1) = (pinvcl _ (inductionCl psing p*cl p1cl pinvcl p+cl x1))  
  inductionCl psing p*cl p1cl pinvcl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p1cl pinvcl p+cl x1) (inductionCl psing p*cl p1cl pinvcl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpNonassociativeNondistributiveRingTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpNonassociativeNondistributiveRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → (( (x1 : (OpNonassociativeNondistributiveRingTerm n)) → ((P x1) → (P (invOL x1)))) → (( (x1 x2 : (OpNonassociativeNondistributiveRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpNonassociativeNondistributiveRingTerm n)) → (P x))))))) 
  inductionOpB pv p*ol p1ol pinvol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p1ol pinvol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p1ol pinvol p+ol x1) (inductionOpB pv p*ol p1ol pinvol p+ol x2))  
  inductionOpB pv p*ol p1ol pinvol p+ol 1OL = p1ol  
  inductionOpB pv p*ol p1ol pinvol p+ol (invOL x1) = (pinvol _ (inductionOpB pv p*ol p1ol pinvol p+ol x1))  
  inductionOpB pv p*ol p1ol pinvol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p1ol pinvol p+ol x1) (inductionOpB pv p*ol p1ol pinvol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpNonassociativeNondistributiveRingTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpNonassociativeNondistributiveRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → (( (x1 : (OpNonassociativeNondistributiveRingTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → (( (x1 x2 : (OpNonassociativeNondistributiveRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpNonassociativeNondistributiveRingTerm2 n A)) → (P x)))))))) 
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x1))  
  inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x2))  
  stageB :  (NonassociativeNondistributiveRingTerm → (Staged NonassociativeNondistributiveRingTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClNonassociativeNondistributiveRingTerm A) → (Staged (ClNonassociativeNondistributiveRingTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpNonassociativeNondistributiveRingTerm n) → (Staged (OpNonassociativeNondistributiveRingTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpNonassociativeNondistributiveRingTerm2 n A) → (Staged (OpNonassociativeNondistributiveRingTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      invT : ((Repr A) → (Repr A)) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 