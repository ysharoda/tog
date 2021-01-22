
module Semiring   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsSemiring  (A : Set) (0ᵢ : A) (+ : (A → (A → A))) (* : (A → (A → A))) (1ᵢ : A) : Set where 
     field  
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ)  
  
  record Semiring  (A : Set) : Set where 
     field  
      0ᵢ : A 
      + : (A → (A → A)) 
      * : (A → (A → A)) 
      1ᵢ : A 
      isSemiring : (IsSemiring A 0ᵢ (+) (*) 1ᵢ)  
  
  open Semiring
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      +S : (AS → (AS → AS)) 
      *S : (AS → (AS → AS)) 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (*P 0P xP) ≡ 0P) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (*P xP 0P) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Se1 : (Semiring A1)) (Se2 : (Semiring A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Se1)) ≡ (0ᵢ Se2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Se1) x1 x2)) ≡ ((+ Se2) (hom x1) (hom x2))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Se1) x1 x2)) ≡ ((* Se2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Se1)) ≡ (1ᵢ Se2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Se1 : (Semiring A1)) (Se2 : (Semiring A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Se1) (0ᵢ Se2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Se1) x1 x2) ((+ Se2) y1 y2))))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Se1) x1 x2) ((* Se2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Se1) (1ᵢ Se2))  
  
  data SemiringTerm   : Set where 
      0L : SemiringTerm 
      +L : (SemiringTerm → (SemiringTerm → SemiringTerm)) 
      *L : (SemiringTerm → (SemiringTerm → SemiringTerm)) 
      1L : SemiringTerm  
      
  data ClSemiringTerm  (A : Set) : Set where 
      sing : (A → (ClSemiringTerm A)) 
      0Cl : (ClSemiringTerm A) 
      +Cl : ((ClSemiringTerm A) → ((ClSemiringTerm A) → (ClSemiringTerm A))) 
      *Cl : ((ClSemiringTerm A) → ((ClSemiringTerm A) → (ClSemiringTerm A))) 
      1Cl : (ClSemiringTerm A)  
      
  data OpSemiringTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpSemiringTerm n)) 
      0OL : (OpSemiringTerm n) 
      +OL : ((OpSemiringTerm n) → ((OpSemiringTerm n) → (OpSemiringTerm n))) 
      *OL : ((OpSemiringTerm n) → ((OpSemiringTerm n) → (OpSemiringTerm n))) 
      1OL : (OpSemiringTerm n)  
      
  data OpSemiringTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpSemiringTerm2 n A)) 
      sing2 : (A → (OpSemiringTerm2 n A)) 
      0OL2 : (OpSemiringTerm2 n A) 
      +OL2 : ((OpSemiringTerm2 n A) → ((OpSemiringTerm2 n A) → (OpSemiringTerm2 n A))) 
      *OL2 : ((OpSemiringTerm2 n A) → ((OpSemiringTerm2 n A) → (OpSemiringTerm2 n A))) 
      1OL2 : (OpSemiringTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClSemiringTerm A) → (ClSemiringTerm A)) 
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (+Cl 0Cl x) = x  
  simplifyCl (+Cl x 0Cl) = x  
  simplifyCl 0Cl = 0Cl  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpSemiringTerm n) → (OpSemiringTerm n)) 
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (+OL 0OL x) = x  
  simplifyOpB (+OL x 0OL) = x  
  simplifyOpB 0OL = 0OL  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpSemiringTerm2 n A) → (OpSemiringTerm2 n A)) 
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (+OL2 0OL2 x) = x  
  simplifyOp (+OL2 x 0OL2) = x  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Semiring A) → (SemiringTerm → A)) 
  evalB Se 0L = (0ᵢ Se)  
  evalB Se (+L x1 x2) = ((+ Se) (evalB Se x1) (evalB Se x2))  
  evalB Se (*L x1 x2) = ((* Se) (evalB Se x1) (evalB Se x2))  
  evalB Se 1L = (1ᵢ Se)  
  evalCl :  {A : Set} →  ((Semiring A) → ((ClSemiringTerm A) → A)) 
  evalCl Se (sing x1) = x1  
  evalCl Se 0Cl = (0ᵢ Se)  
  evalCl Se (+Cl x1 x2) = ((+ Se) (evalCl Se x1) (evalCl Se x2))  
  evalCl Se (*Cl x1 x2) = ((* Se) (evalCl Se x1) (evalCl Se x2))  
  evalCl Se 1Cl = (1ᵢ Se)  
  evalOpB :  {A : Set} {n : Nat} →  ((Semiring A) → ((Vec A n) → ((OpSemiringTerm n) → A))) 
  evalOpB Se vars (v x1) = (lookup vars x1)  
  evalOpB Se vars 0OL = (0ᵢ Se)  
  evalOpB Se vars (+OL x1 x2) = ((+ Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  evalOpB Se vars (*OL x1 x2) = ((* Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  evalOpB Se vars 1OL = (1ᵢ Se)  
  evalOp :  {A : Set} {n : Nat} →  ((Semiring A) → ((Vec A n) → ((OpSemiringTerm2 n A) → A))) 
  evalOp Se vars (v2 x1) = (lookup vars x1)  
  evalOp Se vars (sing2 x1) = x1  
  evalOp Se vars 0OL2 = (0ᵢ Se)  
  evalOp Se vars (+OL2 x1 x2) = ((+ Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  evalOp Se vars (*OL2 x1 x2) = ((* Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  evalOp Se vars 1OL2 = (1ᵢ Se)  
  inductionB :  {P : (SemiringTerm → Set)} →  ((P 0L) → (( (x1 x2 : SemiringTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 x2 : SemiringTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P 1L) → ( (x : SemiringTerm) → (P x)))))) 
  inductionB p0l p+l p*l p1l 0L = p0l  
  inductionB p0l p+l p*l p1l (+L x1 x2) = (p+l _ _ (inductionB p0l p+l p*l p1l x1) (inductionB p0l p+l p*l p1l x2))  
  inductionB p0l p+l p*l p1l (*L x1 x2) = (p*l _ _ (inductionB p0l p+l p*l p1l x1) (inductionB p0l p+l p*l p1l x2))  
  inductionB p0l p+l p*l p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClSemiringTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClSemiringTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 x2 : (ClSemiringTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P 1Cl) → ( (x : (ClSemiringTerm A)) → (P x))))))) 
  inductionCl psing p0cl p+cl p*cl p1cl (sing x1) = (psing x1)  
  inductionCl psing p0cl p+cl p*cl p1cl 0Cl = p0cl  
  inductionCl psing p0cl p+cl p*cl p1cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p0cl p+cl p*cl p1cl x1) (inductionCl psing p0cl p+cl p*cl p1cl x2))  
  inductionCl psing p0cl p+cl p*cl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p0cl p+cl p*cl p1cl x1) (inductionCl psing p0cl p+cl p*cl p1cl x2))  
  inductionCl psing p0cl p+cl p*cl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpSemiringTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpSemiringTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 x2 : (OpSemiringTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P 1OL) → ( (x : (OpSemiringTerm n)) → (P x))))))) 
  inductionOpB pv p0ol p+ol p*ol p1ol (v x1) = (pv x1)  
  inductionOpB pv p0ol p+ol p*ol p1ol 0OL = p0ol  
  inductionOpB pv p0ol p+ol p*ol p1ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p0ol p+ol p*ol p1ol x1) (inductionOpB pv p0ol p+ol p*ol p1ol x2))  
  inductionOpB pv p0ol p+ol p*ol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p0ol p+ol p*ol p1ol x1) (inductionOpB pv p0ol p+ol p*ol p1ol x2))  
  inductionOpB pv p0ol p+ol p*ol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpSemiringTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpSemiringTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 x2 : (OpSemiringTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P 1OL2) → ( (x : (OpSemiringTerm2 n A)) → (P x)))))))) 
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 x1) (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 x2))  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 x1) (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 x2))  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 p1ol2 1OL2 = p1ol2  
  stageB :  (SemiringTerm → (Staged SemiringTerm))
  stageB 0L = (Now 0L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClSemiringTerm A) → (Staged (ClSemiringTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpSemiringTerm n) → (Staged (OpSemiringTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpSemiringTerm2 n A) → (Staged (OpSemiringTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A)  
  
 