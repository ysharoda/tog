
module Rng   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Rng  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      neg : (A → A) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      * : (A → (A → A)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x)))  
  
  open Rng
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS)) 
      0S : AS 
      negS : (AS → AS) 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Rn1 : (Rng A1)) (Rn2 : (Rng A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Rn1) x1 x2)) ≡ ((+ Rn2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Rn1)) ≡ (0ᵢ Rn2) 
      pres-neg : ( {x1 : A1} → (hom ((neg Rn1) x1)) ≡ ((neg Rn2) (hom x1))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Rn1) x1 x2)) ≡ ((* Rn2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Rn1 : (Rng A1)) (Rn2 : (Rng A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Rn1) x1 x2) ((+ Rn2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Rn1) (0ᵢ Rn2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Rn1) x1) ((neg Rn2) y1)))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Rn1) x1 x2) ((* Rn2) y1 y2)))))  
  
  data RngTerm   : Set where 
      +L : (RngTerm → (RngTerm → RngTerm)) 
      0L : RngTerm 
      negL : (RngTerm → RngTerm) 
      *L : (RngTerm → (RngTerm → RngTerm))  
      
  data ClRngTerm  (A : Set) : Set where 
      sing : (A → (ClRngTerm A)) 
      +Cl : ((ClRngTerm A) → ((ClRngTerm A) → (ClRngTerm A))) 
      0Cl : (ClRngTerm A) 
      negCl : ((ClRngTerm A) → (ClRngTerm A)) 
      *Cl : ((ClRngTerm A) → ((ClRngTerm A) → (ClRngTerm A)))  
      
  data OpRngTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRngTerm n)) 
      +OL : ((OpRngTerm n) → ((OpRngTerm n) → (OpRngTerm n))) 
      0OL : (OpRngTerm n) 
      negOL : ((OpRngTerm n) → (OpRngTerm n)) 
      *OL : ((OpRngTerm n) → ((OpRngTerm n) → (OpRngTerm n)))  
      
  data OpRngTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRngTerm2 n A)) 
      sing2 : (A → (OpRngTerm2 n A)) 
      +OL2 : ((OpRngTerm2 n A) → ((OpRngTerm2 n A) → (OpRngTerm2 n A))) 
      0OL2 : (OpRngTerm2 n A) 
      negOL2 : ((OpRngTerm2 n A) → (OpRngTerm2 n A)) 
      *OL2 : ((OpRngTerm2 n A) → ((OpRngTerm2 n A) → (OpRngTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClRngTerm A) → (ClRngTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (negCl x1) = (negCl (simplifyCl _ x1))  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpRngTerm n) → (OpRngTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (negOL x1) = (negOL (simplifyOpB _ x1))  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpRngTerm2 n A) → (OpRngTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (negOL2 x1) = (negOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Rng A) → (RngTerm → A)) 
  evalB Rn (+L x1 x2) = ((+ Rn) (evalB Rn x1) (evalB Rn x2))  
  evalB Rn 0L = (0ᵢ Rn)  
  evalB Rn (negL x1) = ((neg Rn) (evalB Rn x1))  
  evalB Rn (*L x1 x2) = ((* Rn) (evalB Rn x1) (evalB Rn x2))  
  evalCl :  {A : Set} →  ((Rng A) → ((ClRngTerm A) → A)) 
  evalCl Rn (sing x1) = x1  
  evalCl Rn (+Cl x1 x2) = ((+ Rn) (evalCl Rn x1) (evalCl Rn x2))  
  evalCl Rn 0Cl = (0ᵢ Rn)  
  evalCl Rn (negCl x1) = ((neg Rn) (evalCl Rn x1))  
  evalCl Rn (*Cl x1 x2) = ((* Rn) (evalCl Rn x1) (evalCl Rn x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Rng A) → ((Vec A n) → ((OpRngTerm n) → A))) 
  evalOpB n Rn vars (v x1) = (lookup vars x1)  
  evalOpB n Rn vars (+OL x1 x2) = ((+ Rn) (evalOpB n Rn vars x1) (evalOpB n Rn vars x2))  
  evalOpB n Rn vars 0OL = (0ᵢ Rn)  
  evalOpB n Rn vars (negOL x1) = ((neg Rn) (evalOpB n Rn vars x1))  
  evalOpB n Rn vars (*OL x1 x2) = ((* Rn) (evalOpB n Rn vars x1) (evalOpB n Rn vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Rng A) → ((Vec A n) → ((OpRngTerm2 n A) → A))) 
  evalOp n Rn vars (v2 x1) = (lookup vars x1)  
  evalOp n Rn vars (sing2 x1) = x1  
  evalOp n Rn vars (+OL2 x1 x2) = ((+ Rn) (evalOp n Rn vars x1) (evalOp n Rn vars x2))  
  evalOp n Rn vars 0OL2 = (0ᵢ Rn)  
  evalOp n Rn vars (negOL2 x1) = ((neg Rn) (evalOp n Rn vars x1))  
  evalOp n Rn vars (*OL2 x1 x2) = ((* Rn) (evalOp n Rn vars x1) (evalOp n Rn vars x2))  
  inductionB :  (P : (RngTerm → Set)) →  (( (x1 x2 : RngTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : RngTerm) → ((P x1) → (P (negL x1)))) → (( (x1 x2 : RngTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : RngTerm) → (P x)))))) 
  inductionB p p+l p0l pnegl p*l (+L x1 x2) = (p+l _ _ (inductionB p p+l p0l pnegl p*l x1) (inductionB p p+l p0l pnegl p*l x2))  
  inductionB p p+l p0l pnegl p*l 0L = p0l  
  inductionB p p+l p0l pnegl p*l (negL x1) = (pnegl _ (inductionB p p+l p0l pnegl p*l x1))  
  inductionB p p+l p0l pnegl p*l (*L x1 x2) = (p*l _ _ (inductionB p p+l p0l pnegl p*l x1) (inductionB p p+l p0l pnegl p*l x2))  
  inductionCl :  (A : Set) (P : ((ClRngTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRngTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClRngTerm A)) → ((P x1) → (P (negCl x1)))) → (( (x1 x2 : (ClRngTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClRngTerm A)) → (P x))))))) 
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl p*cl x1) (inductionCl _ p psing p+cl p0cl pnegcl p*cl x2))  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl 0Cl = p0cl  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (negCl x1) = (pnegcl _ (inductionCl _ p psing p+cl p0cl pnegcl p*cl x1))  
  inductionCl _ p psing p+cl p0cl pnegcl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl p*cl x1) (inductionCl _ p psing p+cl p0cl pnegcl p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpRngTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRngTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpRngTerm n)) → ((P x1) → (P (negOL x1)))) → (( (x1 x2 : (OpRngTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpRngTerm n)) → (P x))))))) 
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol p0ol pnegol p*ol x1) (inductionOpB _ p pv p+ol p0ol pnegol p*ol x2))  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol 0OL = p0ol  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (negOL x1) = (pnegol _ (inductionOpB _ p pv p+ol p0ol pnegol p*ol x1))  
  inductionOpB _ p pv p+ol p0ol pnegol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p+ol p0ol pnegol p*ol x1) (inductionOpB _ p pv p+ol p0ol pnegol p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpRngTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRngTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpRngTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → (( (x1 x2 : (OpRngTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpRngTerm2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x2))  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (negOL2 x1) = (pnegol2 _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x1))  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 p*ol2 x2))  
  stageB :  (RngTerm → (Staged RngTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClRngTerm A) → (Staged (ClRngTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl _ x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpRngTerm n) → (Staged (OpRngTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB _ x1))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpRngTerm2 n A) → (Staged (OpRngTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp _ _ x1))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A)) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 