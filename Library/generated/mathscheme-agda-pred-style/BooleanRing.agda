
module BooleanRing   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsBooleanRing  (A : Set) (* : (A → (A → A))) (1ᵢ : A) (+ : (A → (A → A))) (0ᵢ : A) (neg : (A → A)) : Set where 
     field  
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ) 
      idempotent_* : ( {x : A} → (* x x) ≡ x)  
  
  record BooleanRing  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      1ᵢ : A 
      + : (A → (A → A)) 
      0ᵢ : A 
      neg : (A → A) 
      isBooleanRing : (IsBooleanRing A (*) 1ᵢ (+) 0ᵢ neg)  
  
  open BooleanRing
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      1S : AS 
      +S : (AS → (AS → AS)) 
      0S : AS 
      negS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP)) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (*P 0P xP) ≡ 0P) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (*P xP 0P) ≡ 0P) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Bo1 : (BooleanRing A1)) (Bo2 : (BooleanRing A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Bo1) x1 x2)) ≡ ((* Bo2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Bo1)) ≡ (1ᵢ Bo2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Bo1) x1 x2)) ≡ ((+ Bo2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Bo1)) ≡ (0ᵢ Bo2) 
      pres-neg : ( {x1 : A1} → (hom ((neg Bo1) x1)) ≡ ((neg Bo2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bo1 : (BooleanRing A1)) (Bo2 : (BooleanRing A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Bo1) x1 x2) ((* Bo2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Bo1) (1ᵢ Bo2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Bo1) x1 x2) ((+ Bo2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Bo1) (0ᵢ Bo2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Bo1) x1) ((neg Bo2) y1))))  
  
  data BooleanRingTerm   : Set where 
      *L : (BooleanRingTerm → (BooleanRingTerm → BooleanRingTerm)) 
      1L : BooleanRingTerm 
      +L : (BooleanRingTerm → (BooleanRingTerm → BooleanRingTerm)) 
      0L : BooleanRingTerm 
      negL : (BooleanRingTerm → BooleanRingTerm)  
      
  data ClBooleanRingTerm  (A : Set) : Set where 
      sing : (A → (ClBooleanRingTerm A)) 
      *Cl : ((ClBooleanRingTerm A) → ((ClBooleanRingTerm A) → (ClBooleanRingTerm A))) 
      1Cl : (ClBooleanRingTerm A) 
      +Cl : ((ClBooleanRingTerm A) → ((ClBooleanRingTerm A) → (ClBooleanRingTerm A))) 
      0Cl : (ClBooleanRingTerm A) 
      negCl : ((ClBooleanRingTerm A) → (ClBooleanRingTerm A))  
      
  data OpBooleanRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBooleanRingTerm n)) 
      *OL : ((OpBooleanRingTerm n) → ((OpBooleanRingTerm n) → (OpBooleanRingTerm n))) 
      1OL : (OpBooleanRingTerm n) 
      +OL : ((OpBooleanRingTerm n) → ((OpBooleanRingTerm n) → (OpBooleanRingTerm n))) 
      0OL : (OpBooleanRingTerm n) 
      negOL : ((OpBooleanRingTerm n) → (OpBooleanRingTerm n))  
      
  data OpBooleanRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBooleanRingTerm2 n A)) 
      sing2 : (A → (OpBooleanRingTerm2 n A)) 
      *OL2 : ((OpBooleanRingTerm2 n A) → ((OpBooleanRingTerm2 n A) → (OpBooleanRingTerm2 n A))) 
      1OL2 : (OpBooleanRingTerm2 n A) 
      +OL2 : ((OpBooleanRingTerm2 n A) → ((OpBooleanRingTerm2 n A) → (OpBooleanRingTerm2 n A))) 
      0OL2 : (OpBooleanRingTerm2 n A) 
      negOL2 : ((OpBooleanRingTerm2 n A) → (OpBooleanRingTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClBooleanRingTerm A) → (ClBooleanRingTerm A)) 
  simplifyCl _ (*Cl 1Cl x) = x  
  simplifyCl _ (*Cl x 1Cl) = x  
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (negCl x1) = (negCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpBooleanRingTerm n) → (OpBooleanRingTerm n)) 
  simplifyOpB _ (*OL 1OL x) = x  
  simplifyOpB _ (*OL x 1OL) = x  
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (negOL x1) = (negOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpBooleanRingTerm2 n A) → (OpBooleanRingTerm2 n A)) 
  simplifyOp _ _ (*OL2 1OL2 x) = x  
  simplifyOp _ _ (*OL2 x 1OL2) = x  
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (negOL2 x1) = (negOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BooleanRing A) → (BooleanRingTerm → A)) 
  evalB Bo (*L x1 x2) = ((* Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 1L = (1ᵢ Bo)  
  evalB Bo (+L x1 x2) = ((+ Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 0L = (0ᵢ Bo)  
  evalB Bo (negL x1) = ((neg Bo) (evalB Bo x1))  
  evalCl :  {A : Set} →  ((BooleanRing A) → ((ClBooleanRingTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo (*Cl x1 x2) = ((* Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 1Cl = (1ᵢ Bo)  
  evalCl Bo (+Cl x1 x2) = ((+ Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 0Cl = (0ᵢ Bo)  
  evalCl Bo (negCl x1) = ((neg Bo) (evalCl Bo x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((BooleanRing A) → ((Vec A n) → ((OpBooleanRingTerm n) → A))) 
  evalOpB n Bo vars (v x1) = (lookup vars x1)  
  evalOpB n Bo vars (*OL x1 x2) = ((* Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOpB n Bo vars 1OL = (1ᵢ Bo)  
  evalOpB n Bo vars (+OL x1 x2) = ((+ Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOpB n Bo vars 0OL = (0ᵢ Bo)  
  evalOpB n Bo vars (negOL x1) = ((neg Bo) (evalOpB n Bo vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((BooleanRing A) → ((Vec A n) → ((OpBooleanRingTerm2 n A) → A))) 
  evalOp n Bo vars (v2 x1) = (lookup vars x1)  
  evalOp n Bo vars (sing2 x1) = x1  
  evalOp n Bo vars (*OL2 x1 x2) = ((* Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  evalOp n Bo vars 1OL2 = (1ᵢ Bo)  
  evalOp n Bo vars (+OL2 x1 x2) = ((+ Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  evalOp n Bo vars 0OL2 = (0ᵢ Bo)  
  evalOp n Bo vars (negOL2 x1) = ((neg Bo) (evalOp n Bo vars x1))  
  inductionB :  (P : (BooleanRingTerm → Set)) →  (( (x1 x2 : BooleanRingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → (( (x1 x2 : BooleanRingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : BooleanRingTerm) → ((P x1) → (P (negL x1)))) → ( (x : BooleanRingTerm) → (P x))))))) 
  inductionB p p*l p1l p+l p0l pnegl (*L x1 x2) = (p*l _ _ (inductionB p p*l p1l p+l p0l pnegl x1) (inductionB p p*l p1l p+l p0l pnegl x2))  
  inductionB p p*l p1l p+l p0l pnegl 1L = p1l  
  inductionB p p*l p1l p+l p0l pnegl (+L x1 x2) = (p+l _ _ (inductionB p p*l p1l p+l p0l pnegl x1) (inductionB p p*l p1l p+l p0l pnegl x2))  
  inductionB p p*l p1l p+l p0l pnegl 0L = p0l  
  inductionB p p*l p1l p+l p0l pnegl (negL x1) = (pnegl _ (inductionB p p*l p1l p+l p0l pnegl x1))  
  inductionCl :  (A : Set) (P : ((ClBooleanRingTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBooleanRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → (( (x1 x2 : (ClBooleanRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClBooleanRingTerm A)) → ((P x1) → (P (negCl x1)))) → ( (x : (ClBooleanRingTerm A)) → (P x)))))))) 
  inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl x1) (inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl x2))  
  inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl 1Cl = p1cl  
  inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl x1) (inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl x2))  
  inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl 0Cl = p0cl  
  inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl (negCl x1) = (pnegcl _ (inductionCl _ p psing p*cl p1cl p+cl p0cl pnegcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpBooleanRingTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBooleanRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → (( (x1 x2 : (OpBooleanRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpBooleanRingTerm n)) → ((P x1) → (P (negOL x1)))) → ( (x : (OpBooleanRingTerm n)) → (P x)))))))) 
  inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol x1) (inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol x2))  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol 1OL = p1ol  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol x1) (inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol x2))  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol 0OL = p0ol  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol (negOL x1) = (pnegol _ (inductionOpB _ p pv p*ol p1ol p+ol p0ol pnegol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpBooleanRingTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBooleanRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → (( (x1 x2 : (OpBooleanRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpBooleanRingTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ( (x : (OpBooleanRingTerm2 n A)) → (P x))))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 1OL2 = p1ol2  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 (negOL2 x1) = (pnegol2 _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 pnegol2 x1))  
  stageB :  (BooleanRingTerm → (Staged BooleanRingTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClBooleanRingTerm A) → (Staged (ClBooleanRingTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpBooleanRingTerm n) → (Staged (OpBooleanRingTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpBooleanRingTerm2 n A) → (Staged (OpBooleanRingTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A))  
  
 