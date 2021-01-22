
module LeftAbsorptionOp   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftAbsorptionOp  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x)  
  
  record LeftAbsorptionOp  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isLeftAbsorptionOp : (IsLeftAbsorptionOp A (*) (+))  
  
  open LeftAbsorptionOp
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftAbsorp_+_*P : ( {xP yP : (Prod A A)} → (+P xP (*P xP yP)) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftAbsorptionOp A1)) (Le2 : (LeftAbsorptionOp A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Le1) x1 x2)) ≡ ((* Le2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Le1) x1 x2)) ≡ ((+ Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftAbsorptionOp A1)) (Le2 : (LeftAbsorptionOp A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Le1) x1 x2) ((* Le2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Le1) x1 x2) ((+ Le2) y1 y2)))))  
  
  data LeftAbsorptionOpTerm   : Set where 
      *L : (LeftAbsorptionOpTerm → (LeftAbsorptionOpTerm → LeftAbsorptionOpTerm)) 
      +L : (LeftAbsorptionOpTerm → (LeftAbsorptionOpTerm → LeftAbsorptionOpTerm))  
      
  data ClLeftAbsorptionOpTerm  (A : Set) : Set where 
      sing : (A → (ClLeftAbsorptionOpTerm A)) 
      *Cl : ((ClLeftAbsorptionOpTerm A) → ((ClLeftAbsorptionOpTerm A) → (ClLeftAbsorptionOpTerm A))) 
      +Cl : ((ClLeftAbsorptionOpTerm A) → ((ClLeftAbsorptionOpTerm A) → (ClLeftAbsorptionOpTerm A)))  
      
  data OpLeftAbsorptionOpTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftAbsorptionOpTerm n)) 
      *OL : ((OpLeftAbsorptionOpTerm n) → ((OpLeftAbsorptionOpTerm n) → (OpLeftAbsorptionOpTerm n))) 
      +OL : ((OpLeftAbsorptionOpTerm n) → ((OpLeftAbsorptionOpTerm n) → (OpLeftAbsorptionOpTerm n)))  
      
  data OpLeftAbsorptionOpTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftAbsorptionOpTerm2 n A)) 
      sing2 : (A → (OpLeftAbsorptionOpTerm2 n A)) 
      *OL2 : ((OpLeftAbsorptionOpTerm2 n A) → ((OpLeftAbsorptionOpTerm2 n A) → (OpLeftAbsorptionOpTerm2 n A))) 
      +OL2 : ((OpLeftAbsorptionOpTerm2 n A) → ((OpLeftAbsorptionOpTerm2 n A) → (OpLeftAbsorptionOpTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLeftAbsorptionOpTerm A) → (ClLeftAbsorptionOpTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLeftAbsorptionOpTerm n) → (OpLeftAbsorptionOpTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLeftAbsorptionOpTerm2 n A) → (OpLeftAbsorptionOpTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftAbsorptionOp A) → (LeftAbsorptionOpTerm → A)) 
  evalB Le (*L x1 x2) = ((* Le) (evalB Le x1) (evalB Le x2))  
  evalB Le (+L x1 x2) = ((+ Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftAbsorptionOp A) → ((ClLeftAbsorptionOpTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (*Cl x1 x2) = ((* Le) (evalCl Le x1) (evalCl Le x2))  
  evalCl Le (+Cl x1 x2) = ((+ Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((LeftAbsorptionOp A) → ((Vec A n) → ((OpLeftAbsorptionOpTerm n) → A))) 
  evalOpB Le vars (v x1) = (lookup vars x1)  
  evalOpB Le vars (*OL x1 x2) = ((* Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOpB Le vars (+OL x1 x2) = ((+ Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((LeftAbsorptionOp A) → ((Vec A n) → ((OpLeftAbsorptionOpTerm2 n A) → A))) 
  evalOp Le vars (v2 x1) = (lookup vars x1)  
  evalOp Le vars (sing2 x1) = x1  
  evalOp Le vars (*OL2 x1 x2) = ((* Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  evalOp Le vars (+OL2 x1 x2) = ((+ Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  inductionB :  {P : (LeftAbsorptionOpTerm → Set)} →  (( (x1 x2 : LeftAbsorptionOpTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : LeftAbsorptionOpTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : LeftAbsorptionOpTerm) → (P x)))) 
  inductionB p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionB p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClLeftAbsorptionOpTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftAbsorptionOpTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClLeftAbsorptionOpTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClLeftAbsorptionOpTerm A)) → (P x))))) 
  inductionCl psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionCl psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLeftAbsorptionOpTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftAbsorptionOpTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpLeftAbsorptionOpTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpLeftAbsorptionOpTerm n)) → (P x))))) 
  inductionOpB pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOpB pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLeftAbsorptionOpTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftAbsorptionOpTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpLeftAbsorptionOpTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpLeftAbsorptionOpTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (LeftAbsorptionOpTerm → (Staged LeftAbsorptionOpTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLeftAbsorptionOpTerm A) → (Staged (ClLeftAbsorptionOpTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLeftAbsorptionOpTerm n) → (Staged (OpLeftAbsorptionOpTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLeftAbsorptionOpTerm2 n A) → (Staged (OpLeftAbsorptionOpTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 