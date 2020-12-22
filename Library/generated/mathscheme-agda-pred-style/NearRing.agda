
module NearRing   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsNearRing  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) (0ᵢ : A) (neg : (A → A)) : Set where 
     field  
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x)))  
  
  record NearRing  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      0ᵢ : A 
      neg : (A → A) 
      isNearRing : (IsNearRing A (*) (+) 0ᵢ neg)  
  
  open NearRing
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      0S : AS 
      negS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ne1 : (NearRing A1)) (Ne2 : (NearRing A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ne1) x1 x2)) ≡ ((* Ne2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ne1) x1 x2)) ≡ ((+ Ne2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Ne1)) ≡ (0ᵢ Ne2) 
      pres-neg : ( {x1 : A1} → (hom ((neg Ne1) x1)) ≡ ((neg Ne2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ne1 : (NearRing A1)) (Ne2 : (NearRing A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ne1) x1 x2) ((* Ne2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ne1) x1 x2) ((+ Ne2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Ne1) (0ᵢ Ne2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Ne1) x1) ((neg Ne2) y1))))  
  
  data NearRingTerm   : Set where 
      *L : (NearRingTerm → (NearRingTerm → NearRingTerm)) 
      +L : (NearRingTerm → (NearRingTerm → NearRingTerm)) 
      0L : NearRingTerm 
      negL : (NearRingTerm → NearRingTerm)  
      
  data ClNearRingTerm  (A : Set) : Set where 
      sing : (A → (ClNearRingTerm A)) 
      *Cl : ((ClNearRingTerm A) → ((ClNearRingTerm A) → (ClNearRingTerm A))) 
      +Cl : ((ClNearRingTerm A) → ((ClNearRingTerm A) → (ClNearRingTerm A))) 
      0Cl : (ClNearRingTerm A) 
      negCl : ((ClNearRingTerm A) → (ClNearRingTerm A))  
      
  data OpNearRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpNearRingTerm n)) 
      *OL : ((OpNearRingTerm n) → ((OpNearRingTerm n) → (OpNearRingTerm n))) 
      +OL : ((OpNearRingTerm n) → ((OpNearRingTerm n) → (OpNearRingTerm n))) 
      0OL : (OpNearRingTerm n) 
      negOL : ((OpNearRingTerm n) → (OpNearRingTerm n))  
      
  data OpNearRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpNearRingTerm2 n A)) 
      sing2 : (A → (OpNearRingTerm2 n A)) 
      *OL2 : ((OpNearRingTerm2 n A) → ((OpNearRingTerm2 n A) → (OpNearRingTerm2 n A))) 
      +OL2 : ((OpNearRingTerm2 n A) → ((OpNearRingTerm2 n A) → (OpNearRingTerm2 n A))) 
      0OL2 : (OpNearRingTerm2 n A) 
      negOL2 : ((OpNearRingTerm2 n A) → (OpNearRingTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClNearRingTerm A) → (ClNearRingTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (negCl x1) = (negCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpNearRingTerm n) → (OpNearRingTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (negOL x1) = (negOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpNearRingTerm2 n A) → (OpNearRingTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (negOL2 x1) = (negOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((NearRing A) → (NearRingTerm → A)) 
  evalB Ne (*L x1 x2) = ((* Ne) (evalB Ne x1) (evalB Ne x2))  
  evalB Ne (+L x1 x2) = ((+ Ne) (evalB Ne x1) (evalB Ne x2))  
  evalB Ne 0L = (0ᵢ Ne)  
  evalB Ne (negL x1) = ((neg Ne) (evalB Ne x1))  
  evalCl :  {A : Set} →  ((NearRing A) → ((ClNearRingTerm A) → A)) 
  evalCl Ne (sing x1) = x1  
  evalCl Ne (*Cl x1 x2) = ((* Ne) (evalCl Ne x1) (evalCl Ne x2))  
  evalCl Ne (+Cl x1 x2) = ((+ Ne) (evalCl Ne x1) (evalCl Ne x2))  
  evalCl Ne 0Cl = (0ᵢ Ne)  
  evalCl Ne (negCl x1) = ((neg Ne) (evalCl Ne x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((NearRing A) → ((Vec A n) → ((OpNearRingTerm n) → A))) 
  evalOpB n Ne vars (v x1) = (lookup vars x1)  
  evalOpB n Ne vars (*OL x1 x2) = ((* Ne) (evalOpB n Ne vars x1) (evalOpB n Ne vars x2))  
  evalOpB n Ne vars (+OL x1 x2) = ((+ Ne) (evalOpB n Ne vars x1) (evalOpB n Ne vars x2))  
  evalOpB n Ne vars 0OL = (0ᵢ Ne)  
  evalOpB n Ne vars (negOL x1) = ((neg Ne) (evalOpB n Ne vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((NearRing A) → ((Vec A n) → ((OpNearRingTerm2 n A) → A))) 
  evalOp n Ne vars (v2 x1) = (lookup vars x1)  
  evalOp n Ne vars (sing2 x1) = x1  
  evalOp n Ne vars (*OL2 x1 x2) = ((* Ne) (evalOp n Ne vars x1) (evalOp n Ne vars x2))  
  evalOp n Ne vars (+OL2 x1 x2) = ((+ Ne) (evalOp n Ne vars x1) (evalOp n Ne vars x2))  
  evalOp n Ne vars 0OL2 = (0ᵢ Ne)  
  evalOp n Ne vars (negOL2 x1) = ((neg Ne) (evalOp n Ne vars x1))  
  inductionB :  (P : (NearRingTerm → Set)) →  (( (x1 x2 : NearRingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : NearRingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : NearRingTerm) → ((P x1) → (P (negL x1)))) → ( (x : NearRingTerm) → (P x)))))) 
  inductionB p p*l p+l p0l pnegl (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l p0l pnegl x1) (inductionB p p*l p+l p0l pnegl x2))  
  inductionB p p*l p+l p0l pnegl (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l p0l pnegl x1) (inductionB p p*l p+l p0l pnegl x2))  
  inductionB p p*l p+l p0l pnegl 0L = p0l  
  inductionB p p*l p+l p0l pnegl (negL x1) = (pnegl _ (inductionB p p*l p+l p0l pnegl x1))  
  inductionCl :  (A : Set) (P : ((ClNearRingTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClNearRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClNearRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClNearRingTerm A)) → ((P x1) → (P (negCl x1)))) → ( (x : (ClNearRingTerm A)) → (P x))))))) 
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl p0cl pnegcl x1) (inductionCl _ p psing p*cl p+cl p0cl pnegcl x2))  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl p0cl pnegcl x1) (inductionCl _ p psing p*cl p+cl p0cl pnegcl x2))  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl 0Cl = p0cl  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (negCl x1) = (pnegcl _ (inductionCl _ p psing p*cl p+cl p0cl pnegcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpNearRingTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpNearRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpNearRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpNearRingTerm n)) → ((P x1) → (P (negOL x1)))) → ( (x : (OpNearRingTerm n)) → (P x))))))) 
  inductionOpB _ p pv p*ol p+ol p0ol pnegol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol p0ol pnegol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol p0ol pnegol x1) (inductionOpB _ p pv p*ol p+ol p0ol pnegol x2))  
  inductionOpB _ p pv p*ol p+ol p0ol pnegol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol p0ol pnegol x1) (inductionOpB _ p pv p*ol p+ol p0ol pnegol x2))  
  inductionOpB _ p pv p*ol p+ol p0ol pnegol 0OL = p0ol  
  inductionOpB _ p pv p*ol p+ol p0ol pnegol (negOL x1) = (pnegol _ (inductionOpB _ p pv p*ol p+ol p0ol pnegol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpNearRingTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpNearRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpNearRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpNearRingTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ( (x : (OpNearRingTerm2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 0OL2 = p0ol2  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (negOL2 x1) = (pnegol2 _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x1))  
  stageB :  (NearRingTerm → (Staged NearRingTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClNearRingTerm A) → (Staged (ClNearRingTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageCl _ (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpNearRingTerm n) → (Staged (OpNearRingTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOpB _ (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpNearRingTerm2 n A) → (Staged (OpNearRingTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  stageOp _ _ (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A))  
  
 