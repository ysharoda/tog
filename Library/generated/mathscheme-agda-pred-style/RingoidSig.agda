
module RingoidSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRingoidSig  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
    
  record RingoidSig  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isRingoidSig : (IsRingoidSig A (*) (+))  
  
  open RingoidSig
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RingoidSig A1)) (Ri2 : (RingoidSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ri1) x1 x2)) ≡ ((* Ri2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ri1) x1 x2)) ≡ ((+ Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RingoidSig A1)) (Ri2 : (RingoidSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ri1) x1 x2) ((* Ri2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ri1) x1 x2) ((+ Ri2) y1 y2)))))  
  
  data RingoidSigTerm   : Set where 
      *L : (RingoidSigTerm → (RingoidSigTerm → RingoidSigTerm)) 
      +L : (RingoidSigTerm → (RingoidSigTerm → RingoidSigTerm))  
      
  data ClRingoidSigTerm  (A : Set) : Set where 
      sing : (A → (ClRingoidSigTerm A)) 
      *Cl : ((ClRingoidSigTerm A) → ((ClRingoidSigTerm A) → (ClRingoidSigTerm A))) 
      +Cl : ((ClRingoidSigTerm A) → ((ClRingoidSigTerm A) → (ClRingoidSigTerm A)))  
      
  data OpRingoidSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRingoidSigTerm n)) 
      *OL : ((OpRingoidSigTerm n) → ((OpRingoidSigTerm n) → (OpRingoidSigTerm n))) 
      +OL : ((OpRingoidSigTerm n) → ((OpRingoidSigTerm n) → (OpRingoidSigTerm n)))  
      
  data OpRingoidSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRingoidSigTerm2 n A)) 
      sing2 : (A → (OpRingoidSigTerm2 n A)) 
      *OL2 : ((OpRingoidSigTerm2 n A) → ((OpRingoidSigTerm2 n A) → (OpRingoidSigTerm2 n A))) 
      +OL2 : ((OpRingoidSigTerm2 n A) → ((OpRingoidSigTerm2 n A) → (OpRingoidSigTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClRingoidSigTerm A) → (ClRingoidSigTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpRingoidSigTerm n) → (OpRingoidSigTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpRingoidSigTerm2 n A) → (OpRingoidSigTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RingoidSig A) → (RingoidSigTerm → A)) 
  evalB Ri (*L x1 x2) = ((* Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (+L x1 x2) = ((+ Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RingoidSig A) → ((ClRingoidSigTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (*Cl x1 x2) = ((* Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (+Cl x1 x2) = ((+ Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((RingoidSig A) → ((Vec A n) → ((OpRingoidSigTerm n) → A))) 
  evalOpB n Ri vars (v x1) = (lookup vars x1)  
  evalOpB n Ri vars (*OL x1 x2) = ((* Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOpB n Ri vars (+OL x1 x2) = ((+ Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((RingoidSig A) → ((Vec A n) → ((OpRingoidSigTerm2 n A) → A))) 
  evalOp n Ri vars (v2 x1) = (lookup vars x1)  
  evalOp n Ri vars (sing2 x1) = x1  
  evalOp n Ri vars (*OL2 x1 x2) = ((* Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  evalOp n Ri vars (+OL2 x1 x2) = ((+ Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  inductionB :  (P : (RingoidSigTerm → Set)) →  (( (x1 x2 : RingoidSigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : RingoidSigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : RingoidSigTerm) → (P x)))) 
  inductionB p p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionB p p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClRingoidSigTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRingoidSigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClRingoidSigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClRingoidSigTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpRingoidSigTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRingoidSigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpRingoidSigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpRingoidSigTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOpB _ p pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpRingoidSigTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpRingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpRingoidSigTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (RingoidSigTerm → (Staged RingoidSigTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClRingoidSigTerm A) → (Staged (ClRingoidSigTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpRingoidSigTerm n) → (Staged (OpRingoidSigTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpRingoidSigTerm2 n A) → (Staged (OpRingoidSigTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 