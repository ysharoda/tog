
module BoundedDistributiveLattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BoundedDistributiveLattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x) 
      leftAbsorp_*_+ : ( {x y : A} → (* x (+ x y)) ≡ x) 
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x) 
      leftModular_*_+ : ( {x y z : A} → (+ (* x y) (* x z)) ≡ (* x (+ y (* x z)))) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z)))  
  
  open BoundedDistributiveLattice
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
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      idempotent_+P : ( {xP : (Prod A A)} → (+P xP xP) ≡ xP) 
      leftAbsorp_*_+P : ( {xP yP : (Prod A A)} → (*P xP (+P xP yP)) ≡ xP) 
      leftAbsorp_+_*P : ( {xP yP : (Prod A A)} → (+P xP (*P xP yP)) ≡ xP) 
      leftModular_*_+P : ( {xP yP zP : (Prod A A)} → (+P (*P xP yP) (*P xP zP)) ≡ (*P xP (+P yP (*P xP zP)))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Bo1 : (BoundedDistributiveLattice A1)) (Bo2 : (BoundedDistributiveLattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Bo1) x1 x2)) ≡ ((* Bo2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Bo1) x1 x2)) ≡ ((+ Bo2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Bo1)) ≡ (0ᵢ Bo2) 
      pres-1 : (hom (1ᵢ Bo1)) ≡ (1ᵢ Bo2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bo1 : (BoundedDistributiveLattice A1)) (Bo2 : (BoundedDistributiveLattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Bo1) x1 x2) ((* Bo2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Bo1) x1 x2) ((+ Bo2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Bo1) (0ᵢ Bo2)) 
      interp-1 : (interp (1ᵢ Bo1) (1ᵢ Bo2))  
  
  data BoundedDistributiveLatticeTerm   : Set where 
      *L : (BoundedDistributiveLatticeTerm → (BoundedDistributiveLatticeTerm → BoundedDistributiveLatticeTerm)) 
      +L : (BoundedDistributiveLatticeTerm → (BoundedDistributiveLatticeTerm → BoundedDistributiveLatticeTerm)) 
      0L : BoundedDistributiveLatticeTerm 
      1L : BoundedDistributiveLatticeTerm  
      
  data ClBoundedDistributiveLatticeTerm  (A : Set) : Set where 
      sing : (A → (ClBoundedDistributiveLatticeTerm A)) 
      *Cl : ((ClBoundedDistributiveLatticeTerm A) → ((ClBoundedDistributiveLatticeTerm A) → (ClBoundedDistributiveLatticeTerm A))) 
      +Cl : ((ClBoundedDistributiveLatticeTerm A) → ((ClBoundedDistributiveLatticeTerm A) → (ClBoundedDistributiveLatticeTerm A))) 
      0Cl : (ClBoundedDistributiveLatticeTerm A) 
      1Cl : (ClBoundedDistributiveLatticeTerm A)  
      
  data OpBoundedDistributiveLatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBoundedDistributiveLatticeTerm n)) 
      *OL : ((OpBoundedDistributiveLatticeTerm n) → ((OpBoundedDistributiveLatticeTerm n) → (OpBoundedDistributiveLatticeTerm n))) 
      +OL : ((OpBoundedDistributiveLatticeTerm n) → ((OpBoundedDistributiveLatticeTerm n) → (OpBoundedDistributiveLatticeTerm n))) 
      0OL : (OpBoundedDistributiveLatticeTerm n) 
      1OL : (OpBoundedDistributiveLatticeTerm n)  
      
  data OpBoundedDistributiveLatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBoundedDistributiveLatticeTerm2 n A)) 
      sing2 : (A → (OpBoundedDistributiveLatticeTerm2 n A)) 
      *OL2 : ((OpBoundedDistributiveLatticeTerm2 n A) → ((OpBoundedDistributiveLatticeTerm2 n A) → (OpBoundedDistributiveLatticeTerm2 n A))) 
      +OL2 : ((OpBoundedDistributiveLatticeTerm2 n A) → ((OpBoundedDistributiveLatticeTerm2 n A) → (OpBoundedDistributiveLatticeTerm2 n A))) 
      0OL2 : (OpBoundedDistributiveLatticeTerm2 n A) 
      1OL2 : (OpBoundedDistributiveLatticeTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClBoundedDistributiveLatticeTerm A) → (ClBoundedDistributiveLatticeTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (*Cl 1Cl x) = x  
  simplifyCl _ (*Cl x 1Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpBoundedDistributiveLatticeTerm n) → (OpBoundedDistributiveLatticeTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (*OL 1OL x) = x  
  simplifyOpB _ (*OL x 1OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpBoundedDistributiveLatticeTerm2 n A) → (OpBoundedDistributiveLatticeTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (*OL2 1OL2 x) = x  
  simplifyOp _ _ (*OL2 x 1OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BoundedDistributiveLattice A) → (BoundedDistributiveLatticeTerm → A)) 
  evalB Bo (*L x1 x2) = ((* Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo (+L x1 x2) = ((+ Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 0L = (0ᵢ Bo)  
  evalB Bo 1L = (1ᵢ Bo)  
  evalCl :  {A : Set} →  ((BoundedDistributiveLattice A) → ((ClBoundedDistributiveLatticeTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo (*Cl x1 x2) = ((* Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo (+Cl x1 x2) = ((+ Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 0Cl = (0ᵢ Bo)  
  evalCl Bo 1Cl = (1ᵢ Bo)  
  evalOpB :  {A : Set} (n : Nat) →  ((BoundedDistributiveLattice A) → ((Vec A n) → ((OpBoundedDistributiveLatticeTerm n) → A))) 
  evalOpB n Bo vars (v x1) = (lookup vars x1)  
  evalOpB n Bo vars (*OL x1 x2) = ((* Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOpB n Bo vars (+OL x1 x2) = ((+ Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOpB n Bo vars 0OL = (0ᵢ Bo)  
  evalOpB n Bo vars 1OL = (1ᵢ Bo)  
  evalOp :  {A : Set} (n : Nat) →  ((BoundedDistributiveLattice A) → ((Vec A n) → ((OpBoundedDistributiveLatticeTerm2 n A) → A))) 
  evalOp n Bo vars (v2 x1) = (lookup vars x1)  
  evalOp n Bo vars (sing2 x1) = x1  
  evalOp n Bo vars (*OL2 x1 x2) = ((* Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  evalOp n Bo vars (+OL2 x1 x2) = ((+ Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  evalOp n Bo vars 0OL2 = (0ᵢ Bo)  
  evalOp n Bo vars 1OL2 = (1ᵢ Bo)  
  inductionB :  (P : (BoundedDistributiveLatticeTerm → Set)) →  (( (x1 x2 : BoundedDistributiveLatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : BoundedDistributiveLatticeTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → ((P 1L) → ( (x : BoundedDistributiveLatticeTerm) → (P x)))))) 
  inductionB p p*l p+l p0l p1l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l p0l p1l x1) (inductionB p p*l p+l p0l p1l x2))  
  inductionB p p*l p+l p0l p1l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l p0l p1l x1) (inductionB p p*l p+l p0l p1l x2))  
  inductionB p p*l p+l p0l p1l 0L = p0l  
  inductionB p p*l p+l p0l p1l 1L = p1l  
  inductionCl :  (A : Set) (P : ((ClBoundedDistributiveLatticeTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBoundedDistributiveLatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClBoundedDistributiveLatticeTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → ((P 1Cl) → ( (x : (ClBoundedDistributiveLatticeTerm A)) → (P x))))))) 
  inductionCl _ p psing p*cl p+cl p0cl p1cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl p0cl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl p0cl p1cl x1) (inductionCl _ p psing p*cl p+cl p0cl p1cl x2))  
  inductionCl _ p psing p*cl p+cl p0cl p1cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl p0cl p1cl x1) (inductionCl _ p psing p*cl p+cl p0cl p1cl x2))  
  inductionCl _ p psing p*cl p+cl p0cl p1cl 0Cl = p0cl  
  inductionCl _ p psing p*cl p+cl p0cl p1cl 1Cl = p1cl  
  inductionOpB :  (n : Nat) (P : ((OpBoundedDistributiveLatticeTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBoundedDistributiveLatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpBoundedDistributiveLatticeTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → ((P 1OL) → ( (x : (OpBoundedDistributiveLatticeTerm n)) → (P x))))))) 
  inductionOpB _ p pv p*ol p+ol p0ol p1ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol p0ol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol p0ol p1ol x1) (inductionOpB _ p pv p*ol p+ol p0ol p1ol x2))  
  inductionOpB _ p pv p*ol p+ol p0ol p1ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol p0ol p1ol x1) (inductionOpB _ p pv p*ol p+ol p0ol p1ol x2))  
  inductionOpB _ p pv p*ol p+ol p0ol p1ol 0OL = p0ol  
  inductionOpB _ p pv p*ol p+ol p0ol p1ol 1OL = p1ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpBoundedDistributiveLatticeTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBoundedDistributiveLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpBoundedDistributiveLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → ((P 1OL2) → ( (x : (OpBoundedDistributiveLatticeTerm2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 p1ol2 1OL2 = p1ol2  
  stageB :  (BoundedDistributiveLatticeTerm → (Staged BoundedDistributiveLatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB 1L = (Now 1L)  
  stageCl :  (A : Set) →  ((ClBoundedDistributiveLatticeTerm A) → (Staged (ClBoundedDistributiveLatticeTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ 1Cl = (Now 1Cl)  
  stageOpB :  (n : Nat) →  ((OpBoundedDistributiveLatticeTerm n) → (Staged (OpBoundedDistributiveLatticeTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ 1OL = (Now 1OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpBoundedDistributiveLatticeTerm2 n A) → (Staged (OpBoundedDistributiveLatticeTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      1T : (Repr A)  
  
 