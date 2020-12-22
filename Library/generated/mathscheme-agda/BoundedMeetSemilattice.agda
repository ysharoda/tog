
module BoundedMeetSemilattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BoundedMeetSemilattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      idempotent_* : ( {x : A} → (* x x) ≡ x)  
  
  open BoundedMeetSemilattice
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Bo1 : (BoundedMeetSemilattice A1)) (Bo2 : (BoundedMeetSemilattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Bo1) x1 x2)) ≡ ((* Bo2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Bo1)) ≡ (1ᵢ Bo2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bo1 : (BoundedMeetSemilattice A1)) (Bo2 : (BoundedMeetSemilattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Bo1) x1 x2) ((* Bo2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Bo1) (1ᵢ Bo2))  
  
  data BoundedMeetSemilatticeTerm   : Set where 
      *L : (BoundedMeetSemilatticeTerm → (BoundedMeetSemilatticeTerm → BoundedMeetSemilatticeTerm)) 
      1L : BoundedMeetSemilatticeTerm  
      
  data ClBoundedMeetSemilatticeTerm  (A : Set) : Set where 
      sing : (A → (ClBoundedMeetSemilatticeTerm A)) 
      *Cl : ((ClBoundedMeetSemilatticeTerm A) → ((ClBoundedMeetSemilatticeTerm A) → (ClBoundedMeetSemilatticeTerm A))) 
      1Cl : (ClBoundedMeetSemilatticeTerm A)  
      
  data OpBoundedMeetSemilatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBoundedMeetSemilatticeTerm n)) 
      *OL : ((OpBoundedMeetSemilatticeTerm n) → ((OpBoundedMeetSemilatticeTerm n) → (OpBoundedMeetSemilatticeTerm n))) 
      1OL : (OpBoundedMeetSemilatticeTerm n)  
      
  data OpBoundedMeetSemilatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBoundedMeetSemilatticeTerm2 n A)) 
      sing2 : (A → (OpBoundedMeetSemilatticeTerm2 n A)) 
      *OL2 : ((OpBoundedMeetSemilatticeTerm2 n A) → ((OpBoundedMeetSemilatticeTerm2 n A) → (OpBoundedMeetSemilatticeTerm2 n A))) 
      1OL2 : (OpBoundedMeetSemilatticeTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClBoundedMeetSemilatticeTerm A) → (ClBoundedMeetSemilatticeTerm A)) 
  simplifyCl _ (*Cl 1Cl x) = x  
  simplifyCl _ (*Cl x 1Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpBoundedMeetSemilatticeTerm n) → (OpBoundedMeetSemilatticeTerm n)) 
  simplifyOpB _ (*OL 1OL x) = x  
  simplifyOpB _ (*OL x 1OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpBoundedMeetSemilatticeTerm2 n A) → (OpBoundedMeetSemilatticeTerm2 n A)) 
  simplifyOp _ _ (*OL2 1OL2 x) = x  
  simplifyOp _ _ (*OL2 x 1OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BoundedMeetSemilattice A) → (BoundedMeetSemilatticeTerm → A)) 
  evalB Bo (*L x1 x2) = ((* Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 1L = (1ᵢ Bo)  
  evalCl :  {A : Set} →  ((BoundedMeetSemilattice A) → ((ClBoundedMeetSemilatticeTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo (*Cl x1 x2) = ((* Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 1Cl = (1ᵢ Bo)  
  evalOpB :  {A : Set} (n : Nat) →  ((BoundedMeetSemilattice A) → ((Vec A n) → ((OpBoundedMeetSemilatticeTerm n) → A))) 
  evalOpB n Bo vars (v x1) = (lookup vars x1)  
  evalOpB n Bo vars (*OL x1 x2) = ((* Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOpB n Bo vars 1OL = (1ᵢ Bo)  
  evalOp :  {A : Set} (n : Nat) →  ((BoundedMeetSemilattice A) → ((Vec A n) → ((OpBoundedMeetSemilatticeTerm2 n A) → A))) 
  evalOp n Bo vars (v2 x1) = (lookup vars x1)  
  evalOp n Bo vars (sing2 x1) = x1  
  evalOp n Bo vars (*OL2 x1 x2) = ((* Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  evalOp n Bo vars 1OL2 = (1ᵢ Bo)  
  inductionB :  (P : (BoundedMeetSemilatticeTerm → Set)) →  (( (x1 x2 : BoundedMeetSemilatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → ( (x : BoundedMeetSemilatticeTerm) → (P x)))) 
  inductionB p p*l p1l (*L x1 x2) = (p*l _ _ (inductionB p p*l p1l x1) (inductionB p p*l p1l x2))  
  inductionB p p*l p1l 1L = p1l  
  inductionCl :  (A : Set) (P : ((ClBoundedMeetSemilatticeTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBoundedMeetSemilatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → ( (x : (ClBoundedMeetSemilatticeTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl p1cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p1cl x1) (inductionCl _ p psing p*cl p1cl x2))  
  inductionCl _ p psing p*cl p1cl 1Cl = p1cl  
  inductionOpB :  (n : Nat) (P : ((OpBoundedMeetSemilatticeTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBoundedMeetSemilatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → ( (x : (OpBoundedMeetSemilatticeTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol p1ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p1ol x1) (inductionOpB _ p pv p*ol p1ol x2))  
  inductionOpB _ p pv p*ol p1ol 1OL = p1ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpBoundedMeetSemilatticeTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBoundedMeetSemilatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → ( (x : (OpBoundedMeetSemilatticeTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 1OL2 = p1ol2  
  stageB :  (BoundedMeetSemilatticeTerm → (Staged BoundedMeetSemilatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageCl :  (A : Set) →  ((ClBoundedMeetSemilatticeTerm A) → (Staged (ClBoundedMeetSemilatticeTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageOpB :  (n : Nat) →  ((OpBoundedMeetSemilatticeTerm n) → (Staged (OpBoundedMeetSemilatticeTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpBoundedMeetSemilatticeTerm2 n A) → (Staged (OpBoundedMeetSemilatticeTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A)  
  
 