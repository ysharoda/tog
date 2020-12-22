
module AssocTimesRingoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAssocTimesRingoid  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z)))  
  
  record AssocTimesRingoid  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isAssocTimesRingoid : (IsAssocTimesRingoid A (*) (+))  
  
  open AssocTimesRingoid
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (As1 : (AssocTimesRingoid A1)) (As2 : (AssocTimesRingoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* As1) x1 x2)) ≡ ((* As2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ As1) x1 x2)) ≡ ((+ As2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (As1 : (AssocTimesRingoid A1)) (As2 : (AssocTimesRingoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* As1) x1 x2) ((* As2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ As1) x1 x2) ((+ As2) y1 y2)))))  
  
  data AssocTimesRingoidTerm   : Set where 
      *L : (AssocTimesRingoidTerm → (AssocTimesRingoidTerm → AssocTimesRingoidTerm)) 
      +L : (AssocTimesRingoidTerm → (AssocTimesRingoidTerm → AssocTimesRingoidTerm))  
      
  data ClAssocTimesRingoidTerm  (A : Set) : Set where 
      sing : (A → (ClAssocTimesRingoidTerm A)) 
      *Cl : ((ClAssocTimesRingoidTerm A) → ((ClAssocTimesRingoidTerm A) → (ClAssocTimesRingoidTerm A))) 
      +Cl : ((ClAssocTimesRingoidTerm A) → ((ClAssocTimesRingoidTerm A) → (ClAssocTimesRingoidTerm A)))  
      
  data OpAssocTimesRingoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAssocTimesRingoidTerm n)) 
      *OL : ((OpAssocTimesRingoidTerm n) → ((OpAssocTimesRingoidTerm n) → (OpAssocTimesRingoidTerm n))) 
      +OL : ((OpAssocTimesRingoidTerm n) → ((OpAssocTimesRingoidTerm n) → (OpAssocTimesRingoidTerm n)))  
      
  data OpAssocTimesRingoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAssocTimesRingoidTerm2 n A)) 
      sing2 : (A → (OpAssocTimesRingoidTerm2 n A)) 
      *OL2 : ((OpAssocTimesRingoidTerm2 n A) → ((OpAssocTimesRingoidTerm2 n A) → (OpAssocTimesRingoidTerm2 n A))) 
      +OL2 : ((OpAssocTimesRingoidTerm2 n A) → ((OpAssocTimesRingoidTerm2 n A) → (OpAssocTimesRingoidTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClAssocTimesRingoidTerm A) → (ClAssocTimesRingoidTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpAssocTimesRingoidTerm n) → (OpAssocTimesRingoidTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpAssocTimesRingoidTerm2 n A) → (OpAssocTimesRingoidTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AssocTimesRingoid A) → (AssocTimesRingoidTerm → A)) 
  evalB As (*L x1 x2) = ((* As) (evalB As x1) (evalB As x2))  
  evalB As (+L x1 x2) = ((+ As) (evalB As x1) (evalB As x2))  
  evalCl :  {A : Set} →  ((AssocTimesRingoid A) → ((ClAssocTimesRingoidTerm A) → A)) 
  evalCl As (sing x1) = x1  
  evalCl As (*Cl x1 x2) = ((* As) (evalCl As x1) (evalCl As x2))  
  evalCl As (+Cl x1 x2) = ((+ As) (evalCl As x1) (evalCl As x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((AssocTimesRingoid A) → ((Vec A n) → ((OpAssocTimesRingoidTerm n) → A))) 
  evalOpB n As vars (v x1) = (lookup vars x1)  
  evalOpB n As vars (*OL x1 x2) = ((* As) (evalOpB n As vars x1) (evalOpB n As vars x2))  
  evalOpB n As vars (+OL x1 x2) = ((+ As) (evalOpB n As vars x1) (evalOpB n As vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((AssocTimesRingoid A) → ((Vec A n) → ((OpAssocTimesRingoidTerm2 n A) → A))) 
  evalOp n As vars (v2 x1) = (lookup vars x1)  
  evalOp n As vars (sing2 x1) = x1  
  evalOp n As vars (*OL2 x1 x2) = ((* As) (evalOp n As vars x1) (evalOp n As vars x2))  
  evalOp n As vars (+OL2 x1 x2) = ((+ As) (evalOp n As vars x1) (evalOp n As vars x2))  
  inductionB :  (P : (AssocTimesRingoidTerm → Set)) →  (( (x1 x2 : AssocTimesRingoidTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : AssocTimesRingoidTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : AssocTimesRingoidTerm) → (P x)))) 
  inductionB p p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionB p p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClAssocTimesRingoidTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAssocTimesRingoidTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClAssocTimesRingoidTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClAssocTimesRingoidTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpAssocTimesRingoidTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAssocTimesRingoidTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpAssocTimesRingoidTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpAssocTimesRingoidTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOpB _ p pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpAssocTimesRingoidTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAssocTimesRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpAssocTimesRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpAssocTimesRingoidTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (AssocTimesRingoidTerm → (Staged AssocTimesRingoidTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClAssocTimesRingoidTerm A) → (Staged (ClAssocTimesRingoidTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpAssocTimesRingoidTerm n) → (Staged (OpAssocTimesRingoidTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpAssocTimesRingoidTerm2 n A) → (Staged (OpAssocTimesRingoidTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 