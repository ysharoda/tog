
module Ringoid0Sig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Ringoid0Sig  (A : Set) : Set where 
     field  
      0ᵢ : A 
      + : (A → (A → A)) 
      * : (A → (A → A))  
  
  open Ringoid0Sig
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      +S : (AS → (AS → AS)) 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (Ringoid0Sig A1)) (Ri2 : (Ringoid0Sig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Ri1)) ≡ (0ᵢ Ri2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ri1) x1 x2)) ≡ ((+ Ri2) (hom x1) (hom x2))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ri1) x1 x2)) ≡ ((* Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (Ringoid0Sig A1)) (Ri2 : (Ringoid0Sig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Ri1) (0ᵢ Ri2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ri1) x1 x2) ((+ Ri2) y1 y2))))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ri1) x1 x2) ((* Ri2) y1 y2)))))  
  
  data Ringoid0SigTerm   : Set where 
      0L : Ringoid0SigTerm 
      +L : (Ringoid0SigTerm → (Ringoid0SigTerm → Ringoid0SigTerm)) 
      *L : (Ringoid0SigTerm → (Ringoid0SigTerm → Ringoid0SigTerm))  
      
  data ClRingoid0SigTerm  (A : Set) : Set where 
      sing : (A → (ClRingoid0SigTerm A)) 
      0Cl : (ClRingoid0SigTerm A) 
      +Cl : ((ClRingoid0SigTerm A) → ((ClRingoid0SigTerm A) → (ClRingoid0SigTerm A))) 
      *Cl : ((ClRingoid0SigTerm A) → ((ClRingoid0SigTerm A) → (ClRingoid0SigTerm A)))  
      
  data OpRingoid0SigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRingoid0SigTerm n)) 
      0OL : (OpRingoid0SigTerm n) 
      +OL : ((OpRingoid0SigTerm n) → ((OpRingoid0SigTerm n) → (OpRingoid0SigTerm n))) 
      *OL : ((OpRingoid0SigTerm n) → ((OpRingoid0SigTerm n) → (OpRingoid0SigTerm n)))  
      
  data OpRingoid0SigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRingoid0SigTerm2 n A)) 
      sing2 : (A → (OpRingoid0SigTerm2 n A)) 
      0OL2 : (OpRingoid0SigTerm2 n A) 
      +OL2 : ((OpRingoid0SigTerm2 n A) → ((OpRingoid0SigTerm2 n A) → (OpRingoid0SigTerm2 n A))) 
      *OL2 : ((OpRingoid0SigTerm2 n A) → ((OpRingoid0SigTerm2 n A) → (OpRingoid0SigTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClRingoid0SigTerm A) → (ClRingoid0SigTerm A)) 
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpRingoid0SigTerm n) → (OpRingoid0SigTerm n)) 
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpRingoid0SigTerm2 n A) → (OpRingoid0SigTerm2 n A)) 
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Ringoid0Sig A) → (Ringoid0SigTerm → A)) 
  evalB Ri 0L = (0ᵢ Ri)  
  evalB Ri (+L x1 x2) = ((+ Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (*L x1 x2) = ((* Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((Ringoid0Sig A) → ((ClRingoid0SigTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri 0Cl = (0ᵢ Ri)  
  evalCl Ri (+Cl x1 x2) = ((+ Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (*Cl x1 x2) = ((* Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Ringoid0Sig A) → ((Vec A n) → ((OpRingoid0SigTerm n) → A))) 
  evalOpB n Ri vars (v x1) = (lookup vars x1)  
  evalOpB n Ri vars 0OL = (0ᵢ Ri)  
  evalOpB n Ri vars (+OL x1 x2) = ((+ Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOpB n Ri vars (*OL x1 x2) = ((* Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Ringoid0Sig A) → ((Vec A n) → ((OpRingoid0SigTerm2 n A) → A))) 
  evalOp n Ri vars (v2 x1) = (lookup vars x1)  
  evalOp n Ri vars (sing2 x1) = x1  
  evalOp n Ri vars 0OL2 = (0ᵢ Ri)  
  evalOp n Ri vars (+OL2 x1 x2) = ((+ Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  evalOp n Ri vars (*OL2 x1 x2) = ((* Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  inductionB :  (P : (Ringoid0SigTerm → Set)) →  ((P 0L) → (( (x1 x2 : Ringoid0SigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 x2 : Ringoid0SigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : Ringoid0SigTerm) → (P x))))) 
  inductionB p p0l p+l p*l 0L = p0l  
  inductionB p p0l p+l p*l (+L x1 x2) = (p+l _ _ (inductionB p p0l p+l p*l x1) (inductionB p p0l p+l p*l x2))  
  inductionB p p0l p+l p*l (*L x1 x2) = (p*l _ _ (inductionB p p0l p+l p*l x1) (inductionB p p0l p+l p*l x2))  
  inductionCl :  (A : Set) (P : ((ClRingoid0SigTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClRingoid0SigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 x2 : (ClRingoid0SigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClRingoid0SigTerm A)) → (P x)))))) 
  inductionCl _ p psing p0cl p+cl p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p0cl p+cl p*cl 0Cl = p0cl  
  inductionCl _ p psing p0cl p+cl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p0cl p+cl p*cl x1) (inductionCl _ p psing p0cl p+cl p*cl x2))  
  inductionCl _ p psing p0cl p+cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p0cl p+cl p*cl x1) (inductionCl _ p psing p0cl p+cl p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpRingoid0SigTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpRingoid0SigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 x2 : (OpRingoid0SigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpRingoid0SigTerm n)) → (P x)))))) 
  inductionOpB _ p pv p0ol p+ol p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p0ol p+ol p*ol 0OL = p0ol  
  inductionOpB _ p pv p0ol p+ol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p0ol p+ol p*ol x1) (inductionOpB _ p pv p0ol p+ol p*ol x2))  
  inductionOpB _ p pv p0ol p+ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p0ol p+ol p*ol x1) (inductionOpB _ p pv p0ol p+ol p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpRingoid0SigTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpRingoid0SigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 x2 : (OpRingoid0SigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpRingoid0SigTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x2))  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x2))  
  stageB :  (Ringoid0SigTerm → (Staged Ringoid0SigTerm))
  stageB 0L = (Now 0L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClRingoid0SigTerm A) → (Staged (ClRingoid0SigTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpRingoid0SigTerm n) → (Staged (OpRingoid0SigTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpRingoid0SigTerm2 n A) → (Staged (OpRingoid0SigTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 