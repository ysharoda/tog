
module Ringoid1Sig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRingoid1Sig  (A : Set) (* : (A → (A → A))) (1ᵢ : A) (+ : (A → (A → A))) : Set where 
    
  record Ringoid1Sig  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      1ᵢ : A 
      + : (A → (A → A)) 
      isRingoid1Sig : (IsRingoid1Sig A (*) 1ᵢ (+))  
  
  open Ringoid1Sig
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      1S : AS 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (Ringoid1Sig A1)) (Ri2 : (Ringoid1Sig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ri1) x1 x2)) ≡ ((* Ri2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Ri1)) ≡ (1ᵢ Ri2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ri1) x1 x2)) ≡ ((+ Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (Ringoid1Sig A1)) (Ri2 : (Ringoid1Sig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ri1) x1 x2) ((* Ri2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Ri1) (1ᵢ Ri2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ri1) x1 x2) ((+ Ri2) y1 y2)))))  
  
  data Ringoid1SigTerm   : Set where 
      *L : (Ringoid1SigTerm → (Ringoid1SigTerm → Ringoid1SigTerm)) 
      1L : Ringoid1SigTerm 
      +L : (Ringoid1SigTerm → (Ringoid1SigTerm → Ringoid1SigTerm))  
      
  data ClRingoid1SigTerm  (A : Set) : Set where 
      sing : (A → (ClRingoid1SigTerm A)) 
      *Cl : ((ClRingoid1SigTerm A) → ((ClRingoid1SigTerm A) → (ClRingoid1SigTerm A))) 
      1Cl : (ClRingoid1SigTerm A) 
      +Cl : ((ClRingoid1SigTerm A) → ((ClRingoid1SigTerm A) → (ClRingoid1SigTerm A)))  
      
  data OpRingoid1SigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRingoid1SigTerm n)) 
      *OL : ((OpRingoid1SigTerm n) → ((OpRingoid1SigTerm n) → (OpRingoid1SigTerm n))) 
      1OL : (OpRingoid1SigTerm n) 
      +OL : ((OpRingoid1SigTerm n) → ((OpRingoid1SigTerm n) → (OpRingoid1SigTerm n)))  
      
  data OpRingoid1SigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRingoid1SigTerm2 n A)) 
      sing2 : (A → (OpRingoid1SigTerm2 n A)) 
      *OL2 : ((OpRingoid1SigTerm2 n A) → ((OpRingoid1SigTerm2 n A) → (OpRingoid1SigTerm2 n A))) 
      1OL2 : (OpRingoid1SigTerm2 n A) 
      +OL2 : ((OpRingoid1SigTerm2 n A) → ((OpRingoid1SigTerm2 n A) → (OpRingoid1SigTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRingoid1SigTerm A) → (ClRingoid1SigTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRingoid1SigTerm n) → (OpRingoid1SigTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRingoid1SigTerm2 n A) → (OpRingoid1SigTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Ringoid1Sig A) → (Ringoid1SigTerm → A)) 
  evalB Ri (*L x1 x2) = ((* Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri 1L = (1ᵢ Ri)  
  evalB Ri (+L x1 x2) = ((+ Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((Ringoid1Sig A) → ((ClRingoid1SigTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (*Cl x1 x2) = ((* Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri 1Cl = (1ᵢ Ri)  
  evalCl Ri (+Cl x1 x2) = ((+ Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Ringoid1Sig A) → ((Vec A n) → ((OpRingoid1SigTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (*OL x1 x2) = ((* Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars 1OL = (1ᵢ Ri)  
  evalOpB Ri vars (+OL x1 x2) = ((+ Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Ringoid1Sig A) → ((Vec A n) → ((OpRingoid1SigTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (*OL2 x1 x2) = ((* Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars 1OL2 = (1ᵢ Ri)  
  evalOp Ri vars (+OL2 x1 x2) = ((+ Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (Ringoid1SigTerm → Set)} →  (( (x1 x2 : Ringoid1SigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → (( (x1 x2 : Ringoid1SigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : Ringoid1SigTerm) → (P x))))) 
  inductionB p*l p1l p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p1l p+l x1) (inductionB p*l p1l p+l x2))  
  inductionB p*l p1l p+l 1L = p1l  
  inductionB p*l p1l p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p1l p+l x1) (inductionB p*l p1l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClRingoid1SigTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRingoid1SigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → (( (x1 x2 : (ClRingoid1SigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClRingoid1SigTerm A)) → (P x)))))) 
  inductionCl psing p*cl p1cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p1cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p1cl p+cl x1) (inductionCl psing p*cl p1cl p+cl x2))  
  inductionCl psing p*cl p1cl p+cl 1Cl = p1cl  
  inductionCl psing p*cl p1cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p1cl p+cl x1) (inductionCl psing p*cl p1cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRingoid1SigTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRingoid1SigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → (( (x1 x2 : (OpRingoid1SigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpRingoid1SigTerm n)) → (P x)))))) 
  inductionOpB pv p*ol p1ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p1ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p1ol p+ol x1) (inductionOpB pv p*ol p1ol p+ol x2))  
  inductionOpB pv p*ol p1ol p+ol 1OL = p1ol  
  inductionOpB pv p*ol p1ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p1ol p+ol x1) (inductionOpB pv p*ol p1ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRingoid1SigTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRingoid1SigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → (( (x1 x2 : (OpRingoid1SigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpRingoid1SigTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p1ol2 p+ol2 x2))  
  stageB :  (Ringoid1SigTerm → (Staged Ringoid1SigTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRingoid1SigTerm A) → (Staged (ClRingoid1SigTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRingoid1SigTerm n) → (Staged (OpRingoid1SigTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRingoid1SigTerm2 n A) → (Staged (OpRingoid1SigTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 