
module AssociativeLeftRingoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAssociativeLeftRingoid  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z)))  
  
  record AssociativeLeftRingoid  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isAssociativeLeftRingoid : (IsAssociativeLeftRingoid A (*) (+))  
  
  open AssociativeLeftRingoid
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (As1 : (AssociativeLeftRingoid A1)) (As2 : (AssociativeLeftRingoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* As1) x1 x2)) ≡ ((* As2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ As1) x1 x2)) ≡ ((+ As2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (As1 : (AssociativeLeftRingoid A1)) (As2 : (AssociativeLeftRingoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* As1) x1 x2) ((* As2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ As1) x1 x2) ((+ As2) y1 y2)))))  
  
  data AssociativeLeftRingoidTerm   : Set where 
      *L : (AssociativeLeftRingoidTerm → (AssociativeLeftRingoidTerm → AssociativeLeftRingoidTerm)) 
      +L : (AssociativeLeftRingoidTerm → (AssociativeLeftRingoidTerm → AssociativeLeftRingoidTerm))  
      
  data ClAssociativeLeftRingoidTerm  (A : Set) : Set where 
      sing : (A → (ClAssociativeLeftRingoidTerm A)) 
      *Cl : ((ClAssociativeLeftRingoidTerm A) → ((ClAssociativeLeftRingoidTerm A) → (ClAssociativeLeftRingoidTerm A))) 
      +Cl : ((ClAssociativeLeftRingoidTerm A) → ((ClAssociativeLeftRingoidTerm A) → (ClAssociativeLeftRingoidTerm A)))  
      
  data OpAssociativeLeftRingoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAssociativeLeftRingoidTerm n)) 
      *OL : ((OpAssociativeLeftRingoidTerm n) → ((OpAssociativeLeftRingoidTerm n) → (OpAssociativeLeftRingoidTerm n))) 
      +OL : ((OpAssociativeLeftRingoidTerm n) → ((OpAssociativeLeftRingoidTerm n) → (OpAssociativeLeftRingoidTerm n)))  
      
  data OpAssociativeLeftRingoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAssociativeLeftRingoidTerm2 n A)) 
      sing2 : (A → (OpAssociativeLeftRingoidTerm2 n A)) 
      *OL2 : ((OpAssociativeLeftRingoidTerm2 n A) → ((OpAssociativeLeftRingoidTerm2 n A) → (OpAssociativeLeftRingoidTerm2 n A))) 
      +OL2 : ((OpAssociativeLeftRingoidTerm2 n A) → ((OpAssociativeLeftRingoidTerm2 n A) → (OpAssociativeLeftRingoidTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClAssociativeLeftRingoidTerm A) → (ClAssociativeLeftRingoidTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAssociativeLeftRingoidTerm n) → (OpAssociativeLeftRingoidTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAssociativeLeftRingoidTerm2 n A) → (OpAssociativeLeftRingoidTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AssociativeLeftRingoid A) → (AssociativeLeftRingoidTerm → A)) 
  evalB As (*L x1 x2) = ((* As) (evalB As x1) (evalB As x2))  
  evalB As (+L x1 x2) = ((+ As) (evalB As x1) (evalB As x2))  
  evalCl :  {A : Set} →  ((AssociativeLeftRingoid A) → ((ClAssociativeLeftRingoidTerm A) → A)) 
  evalCl As (sing x1) = x1  
  evalCl As (*Cl x1 x2) = ((* As) (evalCl As x1) (evalCl As x2))  
  evalCl As (+Cl x1 x2) = ((+ As) (evalCl As x1) (evalCl As x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((AssociativeLeftRingoid A) → ((Vec A n) → ((OpAssociativeLeftRingoidTerm n) → A))) 
  evalOpB As vars (v x1) = (lookup vars x1)  
  evalOpB As vars (*OL x1 x2) = ((* As) (evalOpB As vars x1) (evalOpB As vars x2))  
  evalOpB As vars (+OL x1 x2) = ((+ As) (evalOpB As vars x1) (evalOpB As vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((AssociativeLeftRingoid A) → ((Vec A n) → ((OpAssociativeLeftRingoidTerm2 n A) → A))) 
  evalOp As vars (v2 x1) = (lookup vars x1)  
  evalOp As vars (sing2 x1) = x1  
  evalOp As vars (*OL2 x1 x2) = ((* As) (evalOp As vars x1) (evalOp As vars x2))  
  evalOp As vars (+OL2 x1 x2) = ((+ As) (evalOp As vars x1) (evalOp As vars x2))  
  inductionB :  {P : (AssociativeLeftRingoidTerm → Set)} →  (( (x1 x2 : AssociativeLeftRingoidTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : AssociativeLeftRingoidTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : AssociativeLeftRingoidTerm) → (P x)))) 
  inductionB p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionB p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClAssociativeLeftRingoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAssociativeLeftRingoidTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClAssociativeLeftRingoidTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClAssociativeLeftRingoidTerm A)) → (P x))))) 
  inductionCl psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionCl psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpAssociativeLeftRingoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAssociativeLeftRingoidTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpAssociativeLeftRingoidTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpAssociativeLeftRingoidTerm n)) → (P x))))) 
  inductionOpB pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOpB pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAssociativeLeftRingoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAssociativeLeftRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpAssociativeLeftRingoidTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpAssociativeLeftRingoidTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (AssociativeLeftRingoidTerm → (Staged AssociativeLeftRingoidTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClAssociativeLeftRingoidTerm A) → (Staged (ClAssociativeLeftRingoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpAssociativeLeftRingoidTerm n) → (Staged (OpAssociativeLeftRingoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpAssociativeLeftRingoidTerm2 n A) → (Staged (OpAssociativeLeftRingoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 