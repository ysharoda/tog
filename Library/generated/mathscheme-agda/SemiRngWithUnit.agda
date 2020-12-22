
module SemiRngWithUnit   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record SemiRngWithUnit  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      + : (A → (A → A)) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x)))  
  
  open SemiRngWithUnit
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      1S : AS 
      +S : (AS → (AS → AS)) 
      0S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Se1 : (SemiRngWithUnit A1)) (Se2 : (SemiRngWithUnit A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Se1) x1 x2)) ≡ ((* Se2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Se1)) ≡ (1ᵢ Se2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Se1) x1 x2)) ≡ ((+ Se2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Se1)) ≡ (0ᵢ Se2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Se1 : (SemiRngWithUnit A1)) (Se2 : (SemiRngWithUnit A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Se1) x1 x2) ((* Se2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Se1) (1ᵢ Se2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Se1) x1 x2) ((+ Se2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Se1) (0ᵢ Se2))  
  
  data SemiRngWithUnitTerm   : Set where 
      *L : (SemiRngWithUnitTerm → (SemiRngWithUnitTerm → SemiRngWithUnitTerm)) 
      1L : SemiRngWithUnitTerm 
      +L : (SemiRngWithUnitTerm → (SemiRngWithUnitTerm → SemiRngWithUnitTerm)) 
      0L : SemiRngWithUnitTerm  
      
  data ClSemiRngWithUnitTerm  (A : Set) : Set where 
      sing : (A → (ClSemiRngWithUnitTerm A)) 
      *Cl : ((ClSemiRngWithUnitTerm A) → ((ClSemiRngWithUnitTerm A) → (ClSemiRngWithUnitTerm A))) 
      1Cl : (ClSemiRngWithUnitTerm A) 
      +Cl : ((ClSemiRngWithUnitTerm A) → ((ClSemiRngWithUnitTerm A) → (ClSemiRngWithUnitTerm A))) 
      0Cl : (ClSemiRngWithUnitTerm A)  
      
  data OpSemiRngWithUnitTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpSemiRngWithUnitTerm n)) 
      *OL : ((OpSemiRngWithUnitTerm n) → ((OpSemiRngWithUnitTerm n) → (OpSemiRngWithUnitTerm n))) 
      1OL : (OpSemiRngWithUnitTerm n) 
      +OL : ((OpSemiRngWithUnitTerm n) → ((OpSemiRngWithUnitTerm n) → (OpSemiRngWithUnitTerm n))) 
      0OL : (OpSemiRngWithUnitTerm n)  
      
  data OpSemiRngWithUnitTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpSemiRngWithUnitTerm2 n A)) 
      sing2 : (A → (OpSemiRngWithUnitTerm2 n A)) 
      *OL2 : ((OpSemiRngWithUnitTerm2 n A) → ((OpSemiRngWithUnitTerm2 n A) → (OpSemiRngWithUnitTerm2 n A))) 
      1OL2 : (OpSemiRngWithUnitTerm2 n A) 
      +OL2 : ((OpSemiRngWithUnitTerm2 n A) → ((OpSemiRngWithUnitTerm2 n A) → (OpSemiRngWithUnitTerm2 n A))) 
      0OL2 : (OpSemiRngWithUnitTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClSemiRngWithUnitTerm A) → (ClSemiRngWithUnitTerm A)) 
  simplifyCl _ (*Cl 1Cl x) = x  
  simplifyCl _ (*Cl x 1Cl) = x  
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpSemiRngWithUnitTerm n) → (OpSemiRngWithUnitTerm n)) 
  simplifyOpB _ (*OL 1OL x) = x  
  simplifyOpB _ (*OL x 1OL) = x  
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpSemiRngWithUnitTerm2 n A) → (OpSemiRngWithUnitTerm2 n A)) 
  simplifyOp _ _ (*OL2 1OL2 x) = x  
  simplifyOp _ _ (*OL2 x 1OL2) = x  
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((SemiRngWithUnit A) → (SemiRngWithUnitTerm → A)) 
  evalB Se (*L x1 x2) = ((* Se) (evalB Se x1) (evalB Se x2))  
  evalB Se 1L = (1ᵢ Se)  
  evalB Se (+L x1 x2) = ((+ Se) (evalB Se x1) (evalB Se x2))  
  evalB Se 0L = (0ᵢ Se)  
  evalCl :  {A : Set} →  ((SemiRngWithUnit A) → ((ClSemiRngWithUnitTerm A) → A)) 
  evalCl Se (sing x1) = x1  
  evalCl Se (*Cl x1 x2) = ((* Se) (evalCl Se x1) (evalCl Se x2))  
  evalCl Se 1Cl = (1ᵢ Se)  
  evalCl Se (+Cl x1 x2) = ((+ Se) (evalCl Se x1) (evalCl Se x2))  
  evalCl Se 0Cl = (0ᵢ Se)  
  evalOpB :  {A : Set} (n : Nat) →  ((SemiRngWithUnit A) → ((Vec A n) → ((OpSemiRngWithUnitTerm n) → A))) 
  evalOpB n Se vars (v x1) = (lookup vars x1)  
  evalOpB n Se vars (*OL x1 x2) = ((* Se) (evalOpB n Se vars x1) (evalOpB n Se vars x2))  
  evalOpB n Se vars 1OL = (1ᵢ Se)  
  evalOpB n Se vars (+OL x1 x2) = ((+ Se) (evalOpB n Se vars x1) (evalOpB n Se vars x2))  
  evalOpB n Se vars 0OL = (0ᵢ Se)  
  evalOp :  {A : Set} (n : Nat) →  ((SemiRngWithUnit A) → ((Vec A n) → ((OpSemiRngWithUnitTerm2 n A) → A))) 
  evalOp n Se vars (v2 x1) = (lookup vars x1)  
  evalOp n Se vars (sing2 x1) = x1  
  evalOp n Se vars (*OL2 x1 x2) = ((* Se) (evalOp n Se vars x1) (evalOp n Se vars x2))  
  evalOp n Se vars 1OL2 = (1ᵢ Se)  
  evalOp n Se vars (+OL2 x1 x2) = ((+ Se) (evalOp n Se vars x1) (evalOp n Se vars x2))  
  evalOp n Se vars 0OL2 = (0ᵢ Se)  
  inductionB :  (P : (SemiRngWithUnitTerm → Set)) →  (( (x1 x2 : SemiRngWithUnitTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → (( (x1 x2 : SemiRngWithUnitTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → ( (x : SemiRngWithUnitTerm) → (P x)))))) 
  inductionB p p*l p1l p+l p0l (*L x1 x2) = (p*l _ _ (inductionB p p*l p1l p+l p0l x1) (inductionB p p*l p1l p+l p0l x2))  
  inductionB p p*l p1l p+l p0l 1L = p1l  
  inductionB p p*l p1l p+l p0l (+L x1 x2) = (p+l _ _ (inductionB p p*l p1l p+l p0l x1) (inductionB p p*l p1l p+l p0l x2))  
  inductionB p p*l p1l p+l p0l 0L = p0l  
  inductionCl :  (A : Set) (P : ((ClSemiRngWithUnitTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClSemiRngWithUnitTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → (( (x1 x2 : (ClSemiRngWithUnitTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → ( (x : (ClSemiRngWithUnitTerm A)) → (P x))))))) 
  inductionCl _ p psing p*cl p1cl p+cl p0cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p1cl p+cl p0cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p1cl p+cl p0cl x1) (inductionCl _ p psing p*cl p1cl p+cl p0cl x2))  
  inductionCl _ p psing p*cl p1cl p+cl p0cl 1Cl = p1cl  
  inductionCl _ p psing p*cl p1cl p+cl p0cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p1cl p+cl p0cl x1) (inductionCl _ p psing p*cl p1cl p+cl p0cl x2))  
  inductionCl _ p psing p*cl p1cl p+cl p0cl 0Cl = p0cl  
  inductionOpB :  (n : Nat) (P : ((OpSemiRngWithUnitTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpSemiRngWithUnitTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → (( (x1 x2 : (OpSemiRngWithUnitTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → ( (x : (OpSemiRngWithUnitTerm n)) → (P x))))))) 
  inductionOpB _ p pv p*ol p1ol p+ol p0ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p1ol p+ol p0ol x1) (inductionOpB _ p pv p*ol p1ol p+ol p0ol x2))  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol 1OL = p1ol  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p1ol p+ol p0ol x1) (inductionOpB _ p pv p*ol p1ol p+ol p0ol x2))  
  inductionOpB _ p pv p*ol p1ol p+ol p0ol 0OL = p0ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpSemiRngWithUnitTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpSemiRngWithUnitTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → (( (x1 x2 : (OpSemiRngWithUnitTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → ( (x : (OpSemiRngWithUnitTerm2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 1OL2 = p1ol2  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 p0ol2 0OL2 = p0ol2  
  stageB :  (SemiRngWithUnitTerm → (Staged SemiRngWithUnitTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageCl :  (A : Set) →  ((ClSemiRngWithUnitTerm A) → (Staged (ClSemiRngWithUnitTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageOpB :  (n : Nat) →  ((OpSemiRngWithUnitTerm n) → (Staged (OpSemiRngWithUnitTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpSemiRngWithUnitTerm2 n A) → (Staged (OpSemiRngWithUnitTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A)  
  
 