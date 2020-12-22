
module BoundedMeetLattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BoundedMeetLattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      + : (A → (A → A)) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x) 
      leftAbsorp_*_+ : ( {x y : A} → (* x (+ x y)) ≡ x) 
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x)  
  
  open BoundedMeetLattice
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
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP)) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      idempotent_+P : ( {xP : (Prod A A)} → (+P xP xP) ≡ xP) 
      leftAbsorp_*_+P : ( {xP yP : (Prod A A)} → (*P xP (+P xP yP)) ≡ xP) 
      leftAbsorp_+_*P : ( {xP yP : (Prod A A)} → (+P xP (*P xP yP)) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Bo1 : (BoundedMeetLattice A1)) (Bo2 : (BoundedMeetLattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Bo1) x1 x2)) ≡ ((* Bo2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Bo1)) ≡ (1ᵢ Bo2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Bo1) x1 x2)) ≡ ((+ Bo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bo1 : (BoundedMeetLattice A1)) (Bo2 : (BoundedMeetLattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Bo1) x1 x2) ((* Bo2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Bo1) (1ᵢ Bo2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Bo1) x1 x2) ((+ Bo2) y1 y2)))))  
  
  data BoundedMeetLatticeTerm   : Set where 
      *L : (BoundedMeetLatticeTerm → (BoundedMeetLatticeTerm → BoundedMeetLatticeTerm)) 
      1L : BoundedMeetLatticeTerm 
      +L : (BoundedMeetLatticeTerm → (BoundedMeetLatticeTerm → BoundedMeetLatticeTerm))  
      
  data ClBoundedMeetLatticeTerm  (A : Set) : Set where 
      sing : (A → (ClBoundedMeetLatticeTerm A)) 
      *Cl : ((ClBoundedMeetLatticeTerm A) → ((ClBoundedMeetLatticeTerm A) → (ClBoundedMeetLatticeTerm A))) 
      1Cl : (ClBoundedMeetLatticeTerm A) 
      +Cl : ((ClBoundedMeetLatticeTerm A) → ((ClBoundedMeetLatticeTerm A) → (ClBoundedMeetLatticeTerm A)))  
      
  data OpBoundedMeetLatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBoundedMeetLatticeTerm n)) 
      *OL : ((OpBoundedMeetLatticeTerm n) → ((OpBoundedMeetLatticeTerm n) → (OpBoundedMeetLatticeTerm n))) 
      1OL : (OpBoundedMeetLatticeTerm n) 
      +OL : ((OpBoundedMeetLatticeTerm n) → ((OpBoundedMeetLatticeTerm n) → (OpBoundedMeetLatticeTerm n)))  
      
  data OpBoundedMeetLatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBoundedMeetLatticeTerm2 n A)) 
      sing2 : (A → (OpBoundedMeetLatticeTerm2 n A)) 
      *OL2 : ((OpBoundedMeetLatticeTerm2 n A) → ((OpBoundedMeetLatticeTerm2 n A) → (OpBoundedMeetLatticeTerm2 n A))) 
      1OL2 : (OpBoundedMeetLatticeTerm2 n A) 
      +OL2 : ((OpBoundedMeetLatticeTerm2 n A) → ((OpBoundedMeetLatticeTerm2 n A) → (OpBoundedMeetLatticeTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClBoundedMeetLatticeTerm A) → (ClBoundedMeetLatticeTerm A)) 
  simplifyCl _ (*Cl 1Cl x) = x  
  simplifyCl _ (*Cl x 1Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpBoundedMeetLatticeTerm n) → (OpBoundedMeetLatticeTerm n)) 
  simplifyOpB _ (*OL 1OL x) = x  
  simplifyOpB _ (*OL x 1OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpBoundedMeetLatticeTerm2 n A) → (OpBoundedMeetLatticeTerm2 n A)) 
  simplifyOp _ _ (*OL2 1OL2 x) = x  
  simplifyOp _ _ (*OL2 x 1OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BoundedMeetLattice A) → (BoundedMeetLatticeTerm → A)) 
  evalB Bo (*L x1 x2) = ((* Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 1L = (1ᵢ Bo)  
  evalB Bo (+L x1 x2) = ((+ Bo) (evalB Bo x1) (evalB Bo x2))  
  evalCl :  {A : Set} →  ((BoundedMeetLattice A) → ((ClBoundedMeetLatticeTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo (*Cl x1 x2) = ((* Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 1Cl = (1ᵢ Bo)  
  evalCl Bo (+Cl x1 x2) = ((+ Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((BoundedMeetLattice A) → ((Vec A n) → ((OpBoundedMeetLatticeTerm n) → A))) 
  evalOpB n Bo vars (v x1) = (lookup vars x1)  
  evalOpB n Bo vars (*OL x1 x2) = ((* Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOpB n Bo vars 1OL = (1ᵢ Bo)  
  evalOpB n Bo vars (+OL x1 x2) = ((+ Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((BoundedMeetLattice A) → ((Vec A n) → ((OpBoundedMeetLatticeTerm2 n A) → A))) 
  evalOp n Bo vars (v2 x1) = (lookup vars x1)  
  evalOp n Bo vars (sing2 x1) = x1  
  evalOp n Bo vars (*OL2 x1 x2) = ((* Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  evalOp n Bo vars 1OL2 = (1ᵢ Bo)  
  evalOp n Bo vars (+OL2 x1 x2) = ((+ Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  inductionB :  (P : (BoundedMeetLatticeTerm → Set)) →  (( (x1 x2 : BoundedMeetLatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → (( (x1 x2 : BoundedMeetLatticeTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : BoundedMeetLatticeTerm) → (P x))))) 
  inductionB p p*l p1l p+l (*L x1 x2) = (p*l _ _ (inductionB p p*l p1l p+l x1) (inductionB p p*l p1l p+l x2))  
  inductionB p p*l p1l p+l 1L = p1l  
  inductionB p p*l p1l p+l (+L x1 x2) = (p+l _ _ (inductionB p p*l p1l p+l x1) (inductionB p p*l p1l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClBoundedMeetLatticeTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBoundedMeetLatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → (( (x1 x2 : (ClBoundedMeetLatticeTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClBoundedMeetLatticeTerm A)) → (P x)))))) 
  inductionCl _ p psing p*cl p1cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p1cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p1cl p+cl x1) (inductionCl _ p psing p*cl p1cl p+cl x2))  
  inductionCl _ p psing p*cl p1cl p+cl 1Cl = p1cl  
  inductionCl _ p psing p*cl p1cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p1cl p+cl x1) (inductionCl _ p psing p*cl p1cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpBoundedMeetLatticeTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBoundedMeetLatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → (( (x1 x2 : (OpBoundedMeetLatticeTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpBoundedMeetLatticeTerm n)) → (P x)))))) 
  inductionOpB _ p pv p*ol p1ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p1ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p1ol p+ol x1) (inductionOpB _ p pv p*ol p1ol p+ol x2))  
  inductionOpB _ p pv p*ol p1ol p+ol 1OL = p1ol  
  inductionOpB _ p pv p*ol p1ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p1ol p+ol x1) (inductionOpB _ p pv p*ol p1ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpBoundedMeetLatticeTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBoundedMeetLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → (( (x1 x2 : (OpBoundedMeetLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpBoundedMeetLatticeTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 1OL2 = p1ol2  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x2))  
  stageB :  (BoundedMeetLatticeTerm → (Staged BoundedMeetLatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClBoundedMeetLatticeTerm A) → (Staged (ClBoundedMeetLatticeTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpBoundedMeetLatticeTerm n) → (Staged (OpBoundedMeetLatticeTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpBoundedMeetLatticeTerm2 n A) → (Staged (OpBoundedMeetLatticeTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 