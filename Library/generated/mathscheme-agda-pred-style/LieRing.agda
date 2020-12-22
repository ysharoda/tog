
module LieRing   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLieRing  (A : Set) (0ᵢ : A) (+ : (A → (A → A))) (* : (A → (A → A))) (neg : (A → A)) (1ᵢ : A) : Set where 
     field  
      jacobian_*_+ : ( {x y z : A} → (+ (+ (* x (* y z)) (* y (* z x))) (* z (* x y))) ≡ 0ᵢ) 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ) 
      antiCommutative : ( {x y : A} → (* x y) ≡ (neg (* y x)))  
  
  record LieRing  (A : Set) : Set where 
     field  
      0ᵢ : A 
      + : (A → (A → A)) 
      * : (A → (A → A)) 
      neg : (A → A) 
      1ᵢ : A 
      isLieRing : (IsLieRing A 0ᵢ (+) (*) neg 1ᵢ)  
  
  open LieRing
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      +S : (AS → (AS → AS)) 
      *S : (AS → (AS → AS)) 
      negS : (AS → AS) 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      negP : ((Prod A A) → (Prod A A)) 
      1P : (Prod A A) 
      jacobian_*_+P : ( {xP yP zP : (Prod A A)} → (+P (+P (*P xP (*P yP zP)) (*P yP (*P zP xP))) (*P zP (*P xP yP))) ≡ 0P) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (*P 0P xP) ≡ 0P) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (*P xP 0P) ≡ 0P) 
      antiCommutativeP : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (negP (*P yP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Li1 : (LieRing A1)) (Li2 : (LieRing A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Li1)) ≡ (0ᵢ Li2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Li1) x1 x2)) ≡ ((+ Li2) (hom x1) (hom x2))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Li1) x1 x2)) ≡ ((* Li2) (hom x1) (hom x2))) 
      pres-neg : ( {x1 : A1} → (hom ((neg Li1) x1)) ≡ ((neg Li2) (hom x1))) 
      pres-1 : (hom (1ᵢ Li1)) ≡ (1ᵢ Li2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Li1 : (LieRing A1)) (Li2 : (LieRing A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Li1) (0ᵢ Li2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Li1) x1 x2) ((+ Li2) y1 y2))))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Li1) x1 x2) ((* Li2) y1 y2))))) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Li1) x1) ((neg Li2) y1)))) 
      interp-1 : (interp (1ᵢ Li1) (1ᵢ Li2))  
  
  data LieRingTerm   : Set where 
      0L : LieRingTerm 
      +L : (LieRingTerm → (LieRingTerm → LieRingTerm)) 
      *L : (LieRingTerm → (LieRingTerm → LieRingTerm)) 
      negL : (LieRingTerm → LieRingTerm) 
      1L : LieRingTerm  
      
  data ClLieRingTerm  (A : Set) : Set where 
      sing : (A → (ClLieRingTerm A)) 
      0Cl : (ClLieRingTerm A) 
      +Cl : ((ClLieRingTerm A) → ((ClLieRingTerm A) → (ClLieRingTerm A))) 
      *Cl : ((ClLieRingTerm A) → ((ClLieRingTerm A) → (ClLieRingTerm A))) 
      negCl : ((ClLieRingTerm A) → (ClLieRingTerm A)) 
      1Cl : (ClLieRingTerm A)  
      
  data OpLieRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLieRingTerm n)) 
      0OL : (OpLieRingTerm n) 
      +OL : ((OpLieRingTerm n) → ((OpLieRingTerm n) → (OpLieRingTerm n))) 
      *OL : ((OpLieRingTerm n) → ((OpLieRingTerm n) → (OpLieRingTerm n))) 
      negOL : ((OpLieRingTerm n) → (OpLieRingTerm n)) 
      1OL : (OpLieRingTerm n)  
      
  data OpLieRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLieRingTerm2 n A)) 
      sing2 : (A → (OpLieRingTerm2 n A)) 
      0OL2 : (OpLieRingTerm2 n A) 
      +OL2 : ((OpLieRingTerm2 n A) → ((OpLieRingTerm2 n A) → (OpLieRingTerm2 n A))) 
      *OL2 : ((OpLieRingTerm2 n A) → ((OpLieRingTerm2 n A) → (OpLieRingTerm2 n A))) 
      negOL2 : ((OpLieRingTerm2 n A) → (OpLieRingTerm2 n A)) 
      1OL2 : (OpLieRingTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClLieRingTerm A) → (ClLieRingTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (*Cl 1Cl x) = x  
  simplifyCl _ (*Cl x 1Cl) = x  
  simplifyCl _ (negCl (*Cl y x)) = (*Cl x y)  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (negCl x1) = (negCl (simplifyCl _ x1))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpLieRingTerm n) → (OpLieRingTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (*OL 1OL x) = x  
  simplifyOpB _ (*OL x 1OL) = x  
  simplifyOpB _ (negOL (*OL y x)) = (*OL x y)  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (negOL x1) = (negOL (simplifyOpB _ x1))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpLieRingTerm2 n A) → (OpLieRingTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (*OL2 1OL2 x) = x  
  simplifyOp _ _ (*OL2 x 1OL2) = x  
  simplifyOp _ _ (negOL2 (*OL2 y x)) = (*OL2 x y)  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (negOL2 x1) = (negOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LieRing A) → (LieRingTerm → A)) 
  evalB Li 0L = (0ᵢ Li)  
  evalB Li (+L x1 x2) = ((+ Li) (evalB Li x1) (evalB Li x2))  
  evalB Li (*L x1 x2) = ((* Li) (evalB Li x1) (evalB Li x2))  
  evalB Li (negL x1) = ((neg Li) (evalB Li x1))  
  evalB Li 1L = (1ᵢ Li)  
  evalCl :  {A : Set} →  ((LieRing A) → ((ClLieRingTerm A) → A)) 
  evalCl Li (sing x1) = x1  
  evalCl Li 0Cl = (0ᵢ Li)  
  evalCl Li (+Cl x1 x2) = ((+ Li) (evalCl Li x1) (evalCl Li x2))  
  evalCl Li (*Cl x1 x2) = ((* Li) (evalCl Li x1) (evalCl Li x2))  
  evalCl Li (negCl x1) = ((neg Li) (evalCl Li x1))  
  evalCl Li 1Cl = (1ᵢ Li)  
  evalOpB :  {A : Set} (n : Nat) →  ((LieRing A) → ((Vec A n) → ((OpLieRingTerm n) → A))) 
  evalOpB n Li vars (v x1) = (lookup vars x1)  
  evalOpB n Li vars 0OL = (0ᵢ Li)  
  evalOpB n Li vars (+OL x1 x2) = ((+ Li) (evalOpB n Li vars x1) (evalOpB n Li vars x2))  
  evalOpB n Li vars (*OL x1 x2) = ((* Li) (evalOpB n Li vars x1) (evalOpB n Li vars x2))  
  evalOpB n Li vars (negOL x1) = ((neg Li) (evalOpB n Li vars x1))  
  evalOpB n Li vars 1OL = (1ᵢ Li)  
  evalOp :  {A : Set} (n : Nat) →  ((LieRing A) → ((Vec A n) → ((OpLieRingTerm2 n A) → A))) 
  evalOp n Li vars (v2 x1) = (lookup vars x1)  
  evalOp n Li vars (sing2 x1) = x1  
  evalOp n Li vars 0OL2 = (0ᵢ Li)  
  evalOp n Li vars (+OL2 x1 x2) = ((+ Li) (evalOp n Li vars x1) (evalOp n Li vars x2))  
  evalOp n Li vars (*OL2 x1 x2) = ((* Li) (evalOp n Li vars x1) (evalOp n Li vars x2))  
  evalOp n Li vars (negOL2 x1) = ((neg Li) (evalOp n Li vars x1))  
  evalOp n Li vars 1OL2 = (1ᵢ Li)  
  inductionB :  (P : (LieRingTerm → Set)) →  ((P 0L) → (( (x1 x2 : LieRingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 x2 : LieRingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 : LieRingTerm) → ((P x1) → (P (negL x1)))) → ((P 1L) → ( (x : LieRingTerm) → (P x))))))) 
  inductionB p p0l p+l p*l pnegl p1l 0L = p0l  
  inductionB p p0l p+l p*l pnegl p1l (+L x1 x2) = (p+l _ _ (inductionB p p0l p+l p*l pnegl p1l x1) (inductionB p p0l p+l p*l pnegl p1l x2))  
  inductionB p p0l p+l p*l pnegl p1l (*L x1 x2) = (p*l _ _ (inductionB p p0l p+l p*l pnegl p1l x1) (inductionB p p0l p+l p*l pnegl p1l x2))  
  inductionB p p0l p+l p*l pnegl p1l (negL x1) = (pnegl _ (inductionB p p0l p+l p*l pnegl p1l x1))  
  inductionB p p0l p+l p*l pnegl p1l 1L = p1l  
  inductionCl :  (A : Set) (P : ((ClLieRingTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClLieRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 x2 : (ClLieRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 : (ClLieRingTerm A)) → ((P x1) → (P (negCl x1)))) → ((P 1Cl) → ( (x : (ClLieRingTerm A)) → (P x)))))))) 
  inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl (sing x1) = (psing x1)  
  inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl 0Cl = p0cl  
  inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl x1) (inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl x2))  
  inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl x1) (inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl x2))  
  inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl (negCl x1) = (pnegcl _ (inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl x1))  
  inductionCl _ p psing p0cl p+cl p*cl pnegcl p1cl 1Cl = p1cl  
  inductionOpB :  (n : Nat) (P : ((OpLieRingTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpLieRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 x2 : (OpLieRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 : (OpLieRingTerm n)) → ((P x1) → (P (negOL x1)))) → ((P 1OL) → ( (x : (OpLieRingTerm n)) → (P x)))))))) 
  inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol (v x1) = (pv x1)  
  inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol 0OL = p0ol  
  inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol x1) (inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol x2))  
  inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol x1) (inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol x2))  
  inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol (negOL x1) = (pnegol _ (inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol x1))  
  inductionOpB _ p pv p0ol p+ol p*ol pnegol p1ol 1OL = p1ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpLieRingTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpLieRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 x2 : (OpLieRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 : (OpLieRingTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ((P 1OL2) → ( (x : (OpLieRingTerm2 n A)) → (P x))))))))) 
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 x1) (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 x2))  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 x1) (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 x2))  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 (negOL2 x1) = (pnegol2 _ (inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 x1))  
  inductionOp _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 pnegol2 p1ol2 1OL2 = p1ol2  
  stageB :  (LieRingTerm → (Staged LieRingTerm))
  stageB 0L = (Now 0L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageB 1L = (Now 1L)  
  stageCl :  (A : Set) →  ((ClLieRingTerm A) → (Staged (ClLieRingTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl _ x1))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageOpB :  (n : Nat) →  ((OpLieRingTerm n) → (Staged (OpLieRingTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB _ x1))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpLieRingTerm2 n A) → (Staged (OpLieRingTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp _ _ x1))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      negT : ((Repr A) → (Repr A)) 
      1T : (Repr A)  
  
 