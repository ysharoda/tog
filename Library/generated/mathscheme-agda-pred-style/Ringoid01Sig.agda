
module Ringoid01Sig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRingoid01Sig  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) (0ᵢ : A) (1ᵢ : A) : Set where 
    
  record Ringoid01Sig  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      0ᵢ : A 
      1ᵢ : A 
      isRingoid01Sig : (IsRingoid01Sig A (*) (+) 0ᵢ 1ᵢ)  
  
  open Ringoid01Sig
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      0S : AS 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      1P : (Prod A A)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (Ringoid01Sig A1)) (Ri2 : (Ringoid01Sig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ri1) x1 x2)) ≡ ((* Ri2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ri1) x1 x2)) ≡ ((+ Ri2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Ri1)) ≡ (0ᵢ Ri2) 
      pres-1 : (hom (1ᵢ Ri1)) ≡ (1ᵢ Ri2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (Ringoid01Sig A1)) (Ri2 : (Ringoid01Sig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ri1) x1 x2) ((* Ri2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ri1) x1 x2) ((+ Ri2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Ri1) (0ᵢ Ri2)) 
      interp-1 : (interp (1ᵢ Ri1) (1ᵢ Ri2))  
  
  data Ringoid01SigTerm   : Set where 
      *L : (Ringoid01SigTerm → (Ringoid01SigTerm → Ringoid01SigTerm)) 
      +L : (Ringoid01SigTerm → (Ringoid01SigTerm → Ringoid01SigTerm)) 
      0L : Ringoid01SigTerm 
      1L : Ringoid01SigTerm  
      
  data ClRingoid01SigTerm  (A : Set) : Set where 
      sing : (A → (ClRingoid01SigTerm A)) 
      *Cl : ((ClRingoid01SigTerm A) → ((ClRingoid01SigTerm A) → (ClRingoid01SigTerm A))) 
      +Cl : ((ClRingoid01SigTerm A) → ((ClRingoid01SigTerm A) → (ClRingoid01SigTerm A))) 
      0Cl : (ClRingoid01SigTerm A) 
      1Cl : (ClRingoid01SigTerm A)  
      
  data OpRingoid01SigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRingoid01SigTerm n)) 
      *OL : ((OpRingoid01SigTerm n) → ((OpRingoid01SigTerm n) → (OpRingoid01SigTerm n))) 
      +OL : ((OpRingoid01SigTerm n) → ((OpRingoid01SigTerm n) → (OpRingoid01SigTerm n))) 
      0OL : (OpRingoid01SigTerm n) 
      1OL : (OpRingoid01SigTerm n)  
      
  data OpRingoid01SigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRingoid01SigTerm2 n A)) 
      sing2 : (A → (OpRingoid01SigTerm2 n A)) 
      *OL2 : ((OpRingoid01SigTerm2 n A) → ((OpRingoid01SigTerm2 n A) → (OpRingoid01SigTerm2 n A))) 
      +OL2 : ((OpRingoid01SigTerm2 n A) → ((OpRingoid01SigTerm2 n A) → (OpRingoid01SigTerm2 n A))) 
      0OL2 : (OpRingoid01SigTerm2 n A) 
      1OL2 : (OpRingoid01SigTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClRingoid01SigTerm A) → (ClRingoid01SigTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 0Cl = 0Cl  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRingoid01SigTerm n) → (OpRingoid01SigTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 0OL = 0OL  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRingoid01SigTerm2 n A) → (OpRingoid01SigTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Ringoid01Sig A) → (Ringoid01SigTerm → A)) 
  evalB Ri (*L x1 x2) = ((* Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (+L x1 x2) = ((+ Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri 0L = (0ᵢ Ri)  
  evalB Ri 1L = (1ᵢ Ri)  
  evalCl :  {A : Set} →  ((Ringoid01Sig A) → ((ClRingoid01SigTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (*Cl x1 x2) = ((* Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (+Cl x1 x2) = ((+ Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri 0Cl = (0ᵢ Ri)  
  evalCl Ri 1Cl = (1ᵢ Ri)  
  evalOpB :  {A : Set} {n : Nat} →  ((Ringoid01Sig A) → ((Vec A n) → ((OpRingoid01SigTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (*OL x1 x2) = ((* Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars (+OL x1 x2) = ((+ Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars 0OL = (0ᵢ Ri)  
  evalOpB Ri vars 1OL = (1ᵢ Ri)  
  evalOp :  {A : Set} {n : Nat} →  ((Ringoid01Sig A) → ((Vec A n) → ((OpRingoid01SigTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (*OL2 x1 x2) = ((* Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars (+OL2 x1 x2) = ((+ Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars 0OL2 = (0ᵢ Ri)  
  evalOp Ri vars 1OL2 = (1ᵢ Ri)  
  inductionB :  {P : (Ringoid01SigTerm → Set)} →  (( (x1 x2 : Ringoid01SigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : Ringoid01SigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → ((P 1L) → ( (x : Ringoid01SigTerm) → (P x)))))) 
  inductionB p*l p+l p0l p1l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l p0l p1l x1) (inductionB p*l p+l p0l p1l x2))  
  inductionB p*l p+l p0l p1l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l p0l p1l x1) (inductionB p*l p+l p0l p1l x2))  
  inductionB p*l p+l p0l p1l 0L = p0l  
  inductionB p*l p+l p0l p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClRingoid01SigTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRingoid01SigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClRingoid01SigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → ((P 1Cl) → ( (x : (ClRingoid01SigTerm A)) → (P x))))))) 
  inductionCl psing p*cl p+cl p0cl p1cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl p0cl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl p0cl p1cl x1) (inductionCl psing p*cl p+cl p0cl p1cl x2))  
  inductionCl psing p*cl p+cl p0cl p1cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl p0cl p1cl x1) (inductionCl psing p*cl p+cl p0cl p1cl x2))  
  inductionCl psing p*cl p+cl p0cl p1cl 0Cl = p0cl  
  inductionCl psing p*cl p+cl p0cl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpRingoid01SigTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRingoid01SigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpRingoid01SigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → ((P 1OL) → ( (x : (OpRingoid01SigTerm n)) → (P x))))))) 
  inductionOpB pv p*ol p+ol p0ol p1ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol p0ol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol p0ol p1ol x1) (inductionOpB pv p*ol p+ol p0ol p1ol x2))  
  inductionOpB pv p*ol p+ol p0ol p1ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol p0ol p1ol x1) (inductionOpB pv p*ol p+ol p0ol p1ol x2))  
  inductionOpB pv p*ol p+ol p0ol p1ol 0OL = p0ol  
  inductionOpB pv p*ol p+ol p0ol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRingoid01SigTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRingoid01SigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpRingoid01SigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → ((P 1OL2) → ( (x : (OpRingoid01SigTerm2 n A)) → (P x)))))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 1OL2 = p1ol2  
  stageB :  (Ringoid01SigTerm → (Staged Ringoid01SigTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClRingoid01SigTerm A) → (Staged (ClRingoid01SigTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpRingoid01SigTerm n) → (Staged (OpRingoid01SigTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpRingoid01SigTerm2 n A) → (Staged (OpRingoid01SigTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      1T : (Repr A)  
  
 