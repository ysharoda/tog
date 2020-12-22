
module SemiRng   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record SemiRng  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x)))  
  
  open SemiRng
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      0S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Se1 : (SemiRng A1)) (Se2 : (SemiRng A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Se1) x1 x2)) ≡ ((* Se2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Se1) x1 x2)) ≡ ((+ Se2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Se1)) ≡ (0ᵢ Se2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Se1 : (SemiRng A1)) (Se2 : (SemiRng A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Se1) x1 x2) ((* Se2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Se1) x1 x2) ((+ Se2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Se1) (0ᵢ Se2))  
  
  data SemiRngTerm   : Set where 
      *L : (SemiRngTerm → (SemiRngTerm → SemiRngTerm)) 
      +L : (SemiRngTerm → (SemiRngTerm → SemiRngTerm)) 
      0L : SemiRngTerm  
      
  data ClSemiRngTerm  (A : Set) : Set where 
      sing : (A → (ClSemiRngTerm A)) 
      *Cl : ((ClSemiRngTerm A) → ((ClSemiRngTerm A) → (ClSemiRngTerm A))) 
      +Cl : ((ClSemiRngTerm A) → ((ClSemiRngTerm A) → (ClSemiRngTerm A))) 
      0Cl : (ClSemiRngTerm A)  
      
  data OpSemiRngTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpSemiRngTerm n)) 
      *OL : ((OpSemiRngTerm n) → ((OpSemiRngTerm n) → (OpSemiRngTerm n))) 
      +OL : ((OpSemiRngTerm n) → ((OpSemiRngTerm n) → (OpSemiRngTerm n))) 
      0OL : (OpSemiRngTerm n)  
      
  data OpSemiRngTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpSemiRngTerm2 n A)) 
      sing2 : (A → (OpSemiRngTerm2 n A)) 
      *OL2 : ((OpSemiRngTerm2 n A) → ((OpSemiRngTerm2 n A) → (OpSemiRngTerm2 n A))) 
      +OL2 : ((OpSemiRngTerm2 n A) → ((OpSemiRngTerm2 n A) → (OpSemiRngTerm2 n A))) 
      0OL2 : (OpSemiRngTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClSemiRngTerm A) → (ClSemiRngTerm A)) 
  simplifyCl _ (+Cl 0Cl x) = x  
  simplifyCl _ (+Cl x 0Cl) = x  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 0Cl = 0Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpSemiRngTerm n) → (OpSemiRngTerm n)) 
  simplifyOpB _ (+OL 0OL x) = x  
  simplifyOpB _ (+OL x 0OL) = x  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 0OL = 0OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpSemiRngTerm2 n A) → (OpSemiRngTerm2 n A)) 
  simplifyOp _ _ (+OL2 0OL2 x) = x  
  simplifyOp _ _ (+OL2 x 0OL2) = x  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 0OL2 = 0OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((SemiRng A) → (SemiRngTerm → A)) 
  evalB Se (*L x1 x2) = ((* Se) (evalB Se x1) (evalB Se x2))  
  evalB Se (+L x1 x2) = ((+ Se) (evalB Se x1) (evalB Se x2))  
  evalB Se 0L = (0ᵢ Se)  
  evalCl :  {A : Set} →  ((SemiRng A) → ((ClSemiRngTerm A) → A)) 
  evalCl Se (sing x1) = x1  
  evalCl Se (*Cl x1 x2) = ((* Se) (evalCl Se x1) (evalCl Se x2))  
  evalCl Se (+Cl x1 x2) = ((+ Se) (evalCl Se x1) (evalCl Se x2))  
  evalCl Se 0Cl = (0ᵢ Se)  
  evalOpB :  {A : Set} (n : Nat) →  ((SemiRng A) → ((Vec A n) → ((OpSemiRngTerm n) → A))) 
  evalOpB n Se vars (v x1) = (lookup vars x1)  
  evalOpB n Se vars (*OL x1 x2) = ((* Se) (evalOpB n Se vars x1) (evalOpB n Se vars x2))  
  evalOpB n Se vars (+OL x1 x2) = ((+ Se) (evalOpB n Se vars x1) (evalOpB n Se vars x2))  
  evalOpB n Se vars 0OL = (0ᵢ Se)  
  evalOp :  {A : Set} (n : Nat) →  ((SemiRng A) → ((Vec A n) → ((OpSemiRngTerm2 n A) → A))) 
  evalOp n Se vars (v2 x1) = (lookup vars x1)  
  evalOp n Se vars (sing2 x1) = x1  
  evalOp n Se vars (*OL2 x1 x2) = ((* Se) (evalOp n Se vars x1) (evalOp n Se vars x2))  
  evalOp n Se vars (+OL2 x1 x2) = ((+ Se) (evalOp n Se vars x1) (evalOp n Se vars x2))  
  evalOp n Se vars 0OL2 = (0ᵢ Se)  
  inductionB :  (P : (SemiRngTerm → Set)) →  (( (x1 x2 : SemiRngTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : SemiRngTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → ( (x : SemiRngTerm) → (P x))))) 
  inductionB p p*l p+l p0l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l p0l x1) (inductionB p p*l p+l p0l x2))  
  inductionB p p*l p+l p0l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l p0l x1) (inductionB p p*l p+l p0l x2))  
  inductionB p p*l p+l p0l 0L = p0l  
  inductionCl :  (A : Set) (P : ((ClSemiRngTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClSemiRngTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClSemiRngTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → ( (x : (ClSemiRngTerm A)) → (P x)))))) 
  inductionCl _ p psing p*cl p+cl p0cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl p0cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl p0cl x1) (inductionCl _ p psing p*cl p+cl p0cl x2))  
  inductionCl _ p psing p*cl p+cl p0cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl p0cl x1) (inductionCl _ p psing p*cl p+cl p0cl x2))  
  inductionCl _ p psing p*cl p+cl p0cl 0Cl = p0cl  
  inductionOpB :  (n : Nat) (P : ((OpSemiRngTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpSemiRngTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpSemiRngTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → ( (x : (OpSemiRngTerm n)) → (P x)))))) 
  inductionOpB _ p pv p*ol p+ol p0ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol p0ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol p0ol x1) (inductionOpB _ p pv p*ol p+ol p0ol x2))  
  inductionOpB _ p pv p*ol p+ol p0ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol p0ol x1) (inductionOpB _ p pv p*ol p+ol p0ol x2))  
  inductionOpB _ p pv p*ol p+ol p0ol 0OL = p0ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpSemiRngTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpSemiRngTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpSemiRngTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → ( (x : (OpSemiRngTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 0OL2 = p0ol2  
  stageB :  (SemiRngTerm → (Staged SemiRngTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageCl :  (A : Set) →  ((ClSemiRngTerm A) → (Staged (ClSemiRngTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 0Cl = (Now 0Cl)  
  stageOpB :  (n : Nat) →  ((OpSemiRngTerm n) → (Staged (OpSemiRngTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 0OL = (Now 0OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpSemiRngTerm2 n A) → (Staged (OpSemiRngTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 0OL2 = (Now 0OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A)  
  
 