
module AbelianAdditiveGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AbelianAdditiveGroup  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      neg : (A → A) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ)  
  
  open AbelianAdditiveGroup
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS)) 
      0S : AS 
      negS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ab1 : (AbelianAdditiveGroup A1)) (Ab2 : (AbelianAdditiveGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ab1) x1 x2)) ≡ ((+ Ab2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Ab1)) ≡ (0ᵢ Ab2) 
      pres-neg : ( {x1 : A1} → (hom ((neg Ab1) x1)) ≡ ((neg Ab2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ab1 : (AbelianAdditiveGroup A1)) (Ab2 : (AbelianAdditiveGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ab1) x1 x2) ((+ Ab2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Ab1) (0ᵢ Ab2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Ab1) x1) ((neg Ab2) y1))))  
  
  data AbelianAdditiveGroupTerm   : Set where 
      +L : (AbelianAdditiveGroupTerm → (AbelianAdditiveGroupTerm → AbelianAdditiveGroupTerm)) 
      0L : AbelianAdditiveGroupTerm 
      negL : (AbelianAdditiveGroupTerm → AbelianAdditiveGroupTerm)  
      
  data ClAbelianAdditiveGroupTerm  (A : Set) : Set where 
      sing : (A → (ClAbelianAdditiveGroupTerm A)) 
      +Cl : ((ClAbelianAdditiveGroupTerm A) → ((ClAbelianAdditiveGroupTerm A) → (ClAbelianAdditiveGroupTerm A))) 
      0Cl : (ClAbelianAdditiveGroupTerm A) 
      negCl : ((ClAbelianAdditiveGroupTerm A) → (ClAbelianAdditiveGroupTerm A))  
      
  data OpAbelianAdditiveGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAbelianAdditiveGroupTerm n)) 
      +OL : ((OpAbelianAdditiveGroupTerm n) → ((OpAbelianAdditiveGroupTerm n) → (OpAbelianAdditiveGroupTerm n))) 
      0OL : (OpAbelianAdditiveGroupTerm n) 
      negOL : ((OpAbelianAdditiveGroupTerm n) → (OpAbelianAdditiveGroupTerm n))  
      
  data OpAbelianAdditiveGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAbelianAdditiveGroupTerm2 n A)) 
      sing2 : (A → (OpAbelianAdditiveGroupTerm2 n A)) 
      +OL2 : ((OpAbelianAdditiveGroupTerm2 n A) → ((OpAbelianAdditiveGroupTerm2 n A) → (OpAbelianAdditiveGroupTerm2 n A))) 
      0OL2 : (OpAbelianAdditiveGroupTerm2 n A) 
      negOL2 : ((OpAbelianAdditiveGroupTerm2 n A) → (OpAbelianAdditiveGroupTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClAbelianAdditiveGroupTerm A) → (ClAbelianAdditiveGroupTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (negCl x1) = (negCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpAbelianAdditiveGroupTerm n) → (OpAbelianAdditiveGroupTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (negOL x1) = (negOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpAbelianAdditiveGroupTerm2 n A) → (OpAbelianAdditiveGroupTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (negOL2 x1) = (negOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AbelianAdditiveGroup A) → (AbelianAdditiveGroupTerm → A)) 
  evalB Ab (+L x1 x2) = ((+ Ab) (evalB Ab x1) (evalB Ab x2))  
  evalB Ab 0L = (0ᵢ Ab)  
  evalB Ab (negL x1) = ((neg Ab) (evalB Ab x1))  
  evalCl :  {A : Set} →  ((AbelianAdditiveGroup A) → ((ClAbelianAdditiveGroupTerm A) → A)) 
  evalCl Ab (sing x1) = x1  
  evalCl Ab (+Cl x1 x2) = ((+ Ab) (evalCl Ab x1) (evalCl Ab x2))  
  evalCl Ab 0Cl = (0ᵢ Ab)  
  evalCl Ab (negCl x1) = ((neg Ab) (evalCl Ab x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((AbelianAdditiveGroup A) → ((Vec A n) → ((OpAbelianAdditiveGroupTerm n) → A))) 
  evalOpB n Ab vars (v x1) = (lookup vars x1)  
  evalOpB n Ab vars (+OL x1 x2) = ((+ Ab) (evalOpB n Ab vars x1) (evalOpB n Ab vars x2))  
  evalOpB n Ab vars 0OL = (0ᵢ Ab)  
  evalOpB n Ab vars (negOL x1) = ((neg Ab) (evalOpB n Ab vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((AbelianAdditiveGroup A) → ((Vec A n) → ((OpAbelianAdditiveGroupTerm2 n A) → A))) 
  evalOp n Ab vars (v2 x1) = (lookup vars x1)  
  evalOp n Ab vars (sing2 x1) = x1  
  evalOp n Ab vars (+OL2 x1 x2) = ((+ Ab) (evalOp n Ab vars x1) (evalOp n Ab vars x2))  
  evalOp n Ab vars 0OL2 = (0ᵢ Ab)  
  evalOp n Ab vars (negOL2 x1) = ((neg Ab) (evalOp n Ab vars x1))  
  inductionB :  (P : (AbelianAdditiveGroupTerm → Set)) →  (( (x1 x2 : AbelianAdditiveGroupTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : AbelianAdditiveGroupTerm) → ((P x1) → (P (negL x1)))) → ( (x : AbelianAdditiveGroupTerm) → (P x))))) 
  inductionB p p+l p0l pnegl (+L x1 x2) = (p+l _ _ (inductionB p p+l p0l pnegl x1) (inductionB p p+l p0l pnegl x2))  
  inductionB p p+l p0l pnegl 0L = p0l  
  inductionB p p+l p0l pnegl (negL x1) = (pnegl _ (inductionB p p+l p0l pnegl x1))  
  inductionCl :  (A : Set) (P : ((ClAbelianAdditiveGroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAbelianAdditiveGroupTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClAbelianAdditiveGroupTerm A)) → ((P x1) → (P (negCl x1)))) → ( (x : (ClAbelianAdditiveGroupTerm A)) → (P x)))))) 
  inductionCl _ p psing p+cl p0cl pnegcl (sing x1) = (psing x1)  
  inductionCl _ p psing p+cl p0cl pnegcl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl x1) (inductionCl _ p psing p+cl p0cl pnegcl x2))  
  inductionCl _ p psing p+cl p0cl pnegcl 0Cl = p0cl  
  inductionCl _ p psing p+cl p0cl pnegcl (negCl x1) = (pnegcl _ (inductionCl _ p psing p+cl p0cl pnegcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpAbelianAdditiveGroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAbelianAdditiveGroupTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpAbelianAdditiveGroupTerm n)) → ((P x1) → (P (negOL x1)))) → ( (x : (OpAbelianAdditiveGroupTerm n)) → (P x)))))) 
  inductionOpB _ p pv p+ol p0ol pnegol (v x1) = (pv x1)  
  inductionOpB _ p pv p+ol p0ol pnegol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol p0ol pnegol x1) (inductionOpB _ p pv p+ol p0ol pnegol x2))  
  inductionOpB _ p pv p+ol p0ol pnegol 0OL = p0ol  
  inductionOpB _ p pv p+ol p0ol pnegol (negOL x1) = (pnegol _ (inductionOpB _ p pv p+ol p0ol pnegol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpAbelianAdditiveGroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAbelianAdditiveGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpAbelianAdditiveGroupTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ( (x : (OpAbelianAdditiveGroupTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x2))  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (negOL2 x1) = (pnegol2 _ (inductionOp _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x1))  
  stageB :  (AbelianAdditiveGroupTerm → (Staged AbelianAdditiveGroupTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClAbelianAdditiveGroupTerm A) → (Staged (ClAbelianAdditiveGroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpAbelianAdditiveGroupTerm n) → (Staged (OpAbelianAdditiveGroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpAbelianAdditiveGroupTerm2 n A) → (Staged (OpAbelianAdditiveGroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A))  
  
 