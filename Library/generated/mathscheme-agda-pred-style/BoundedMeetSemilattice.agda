
module BoundedMeetSemilattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsBoundedMeetSemilattice  (A : Set) (* : (A → (A → A))) (1ᵢ : A) : Set where 
     field  
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      idempotent_* : ( {x : A} → (* x x) ≡ x)  
  
  record BoundedMeetSemilattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      1ᵢ : A 
      isBoundedMeetSemilattice : (IsBoundedMeetSemilattice A (*) 1ᵢ)  
  
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
      
  simplifyCl :  {A : Set} →  ((ClBoundedMeetSemilatticeTerm A) → (ClBoundedMeetSemilatticeTerm A)) 
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpBoundedMeetSemilatticeTerm n) → (OpBoundedMeetSemilatticeTerm n)) 
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpBoundedMeetSemilatticeTerm2 n A) → (OpBoundedMeetSemilatticeTerm2 n A)) 
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BoundedMeetSemilattice A) → (BoundedMeetSemilatticeTerm → A)) 
  evalB Bo (*L x1 x2) = ((* Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 1L = (1ᵢ Bo)  
  evalCl :  {A : Set} →  ((BoundedMeetSemilattice A) → ((ClBoundedMeetSemilatticeTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo (*Cl x1 x2) = ((* Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 1Cl = (1ᵢ Bo)  
  evalOpB :  {A : Set} {n : Nat} →  ((BoundedMeetSemilattice A) → ((Vec A n) → ((OpBoundedMeetSemilatticeTerm n) → A))) 
  evalOpB Bo vars (v x1) = (lookup vars x1)  
  evalOpB Bo vars (*OL x1 x2) = ((* Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  evalOpB Bo vars 1OL = (1ᵢ Bo)  
  evalOp :  {A : Set} {n : Nat} →  ((BoundedMeetSemilattice A) → ((Vec A n) → ((OpBoundedMeetSemilatticeTerm2 n A) → A))) 
  evalOp Bo vars (v2 x1) = (lookup vars x1)  
  evalOp Bo vars (sing2 x1) = x1  
  evalOp Bo vars (*OL2 x1 x2) = ((* Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  evalOp Bo vars 1OL2 = (1ᵢ Bo)  
  inductionB :  {P : (BoundedMeetSemilatticeTerm → Set)} →  (( (x1 x2 : BoundedMeetSemilatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → ( (x : BoundedMeetSemilatticeTerm) → (P x)))) 
  inductionB p*l p1l (*L x1 x2) = (p*l _ _ (inductionB p*l p1l x1) (inductionB p*l p1l x2))  
  inductionB p*l p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClBoundedMeetSemilatticeTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBoundedMeetSemilatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → ( (x : (ClBoundedMeetSemilatticeTerm A)) → (P x))))) 
  inductionCl psing p*cl p1cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p1cl x1) (inductionCl psing p*cl p1cl x2))  
  inductionCl psing p*cl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpBoundedMeetSemilatticeTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBoundedMeetSemilatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → ( (x : (OpBoundedMeetSemilatticeTerm n)) → (P x))))) 
  inductionOpB pv p*ol p1ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p1ol x1) (inductionOpB pv p*ol p1ol x2))  
  inductionOpB pv p*ol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpBoundedMeetSemilatticeTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBoundedMeetSemilatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → ( (x : (OpBoundedMeetSemilatticeTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p1ol2 1OL2 = p1ol2  
  stageB :  (BoundedMeetSemilatticeTerm → (Staged BoundedMeetSemilatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClBoundedMeetSemilatticeTerm A) → (Staged (ClBoundedMeetSemilatticeTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpBoundedMeetSemilatticeTerm n) → (Staged (OpBoundedMeetSemilatticeTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpBoundedMeetSemilatticeTerm2 n A) → (Staged (OpBoundedMeetSemilatticeTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A)  
  
 