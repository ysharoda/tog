
module DoubleMonoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record DoubleMonoid  (A : Set) : Set where 
     field  
      0ᵢ : A 
      + : (A → (A → A)) 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      1ᵢ : A 
      * : (A → (A → A)) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z)))  
  
  open DoubleMonoid
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      +S : (AS → (AS → AS)) 
      1S : AS 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Do1 : (DoubleMonoid A1)) (Do2 : (DoubleMonoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Do1)) ≡ (0ᵢ Do2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Do1) x1 x2)) ≡ ((+ Do2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Do1)) ≡ (1ᵢ Do2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Do1) x1 x2)) ≡ ((* Do2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Do1 : (DoubleMonoid A1)) (Do2 : (DoubleMonoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Do1) (0ᵢ Do2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Do1) x1 x2) ((+ Do2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Do1) (1ᵢ Do2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Do1) x1 x2) ((* Do2) y1 y2)))))  
  
  data DoubleMonoidTerm   : Set where 
      0L : DoubleMonoidTerm 
      +L : (DoubleMonoidTerm → (DoubleMonoidTerm → DoubleMonoidTerm)) 
      1L : DoubleMonoidTerm 
      *L : (DoubleMonoidTerm → (DoubleMonoidTerm → DoubleMonoidTerm))  
      
  data ClDoubleMonoidTerm  (A : Set) : Set where 
      sing : (A → (ClDoubleMonoidTerm A)) 
      0Cl : (ClDoubleMonoidTerm A) 
      +Cl : ((ClDoubleMonoidTerm A) → ((ClDoubleMonoidTerm A) → (ClDoubleMonoidTerm A))) 
      1Cl : (ClDoubleMonoidTerm A) 
      *Cl : ((ClDoubleMonoidTerm A) → ((ClDoubleMonoidTerm A) → (ClDoubleMonoidTerm A)))  
      
  data OpDoubleMonoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpDoubleMonoidTerm n)) 
      0OL : (OpDoubleMonoidTerm n) 
      +OL : ((OpDoubleMonoidTerm n) → ((OpDoubleMonoidTerm n) → (OpDoubleMonoidTerm n))) 
      1OL : (OpDoubleMonoidTerm n) 
      *OL : ((OpDoubleMonoidTerm n) → ((OpDoubleMonoidTerm n) → (OpDoubleMonoidTerm n)))  
      
  data OpDoubleMonoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpDoubleMonoidTerm2 n A)) 
      sing2 : (A → (OpDoubleMonoidTerm2 n A)) 
      0OL2 : (OpDoubleMonoidTerm2 n A) 
      +OL2 : ((OpDoubleMonoidTerm2 n A) → ((OpDoubleMonoidTerm2 n A) → (OpDoubleMonoidTerm2 n A))) 
      1OL2 : (OpDoubleMonoidTerm2 n A) 
      *OL2 : ((OpDoubleMonoidTerm2 n A) → ((OpDoubleMonoidTerm2 n A) → (OpDoubleMonoidTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClDoubleMonoidTerm A) → (ClDoubleMonoidTerm A)) 
  simplifyCl (+Cl 0Cl x) = x  
  simplifyCl (+Cl x 0Cl) = x  
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl 0Cl = 0Cl  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpDoubleMonoidTerm n) → (OpDoubleMonoidTerm n)) 
  simplifyOpB (+OL 0OL x) = x  
  simplifyOpB (+OL x 0OL) = x  
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB 0OL = 0OL  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpDoubleMonoidTerm2 n A) → (OpDoubleMonoidTerm2 n A)) 
  simplifyOp (+OL2 0OL2 x) = x  
  simplifyOp (+OL2 x 0OL2) = x  
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((DoubleMonoid A) → (DoubleMonoidTerm → A)) 
  evalB Do 0L = (0ᵢ Do)  
  evalB Do (+L x1 x2) = ((+ Do) (evalB Do x1) (evalB Do x2))  
  evalB Do 1L = (1ᵢ Do)  
  evalB Do (*L x1 x2) = ((* Do) (evalB Do x1) (evalB Do x2))  
  evalCl :  {A : Set} →  ((DoubleMonoid A) → ((ClDoubleMonoidTerm A) → A)) 
  evalCl Do (sing x1) = x1  
  evalCl Do 0Cl = (0ᵢ Do)  
  evalCl Do (+Cl x1 x2) = ((+ Do) (evalCl Do x1) (evalCl Do x2))  
  evalCl Do 1Cl = (1ᵢ Do)  
  evalCl Do (*Cl x1 x2) = ((* Do) (evalCl Do x1) (evalCl Do x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((DoubleMonoid A) → ((Vec A n) → ((OpDoubleMonoidTerm n) → A))) 
  evalOpB Do vars (v x1) = (lookup vars x1)  
  evalOpB Do vars 0OL = (0ᵢ Do)  
  evalOpB Do vars (+OL x1 x2) = ((+ Do) (evalOpB Do vars x1) (evalOpB Do vars x2))  
  evalOpB Do vars 1OL = (1ᵢ Do)  
  evalOpB Do vars (*OL x1 x2) = ((* Do) (evalOpB Do vars x1) (evalOpB Do vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((DoubleMonoid A) → ((Vec A n) → ((OpDoubleMonoidTerm2 n A) → A))) 
  evalOp Do vars (v2 x1) = (lookup vars x1)  
  evalOp Do vars (sing2 x1) = x1  
  evalOp Do vars 0OL2 = (0ᵢ Do)  
  evalOp Do vars (+OL2 x1 x2) = ((+ Do) (evalOp Do vars x1) (evalOp Do vars x2))  
  evalOp Do vars 1OL2 = (1ᵢ Do)  
  evalOp Do vars (*OL2 x1 x2) = ((* Do) (evalOp Do vars x1) (evalOp Do vars x2))  
  inductionB :  {P : (DoubleMonoidTerm → Set)} →  ((P 0L) → (( (x1 x2 : DoubleMonoidTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 1L) → (( (x1 x2 : DoubleMonoidTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : DoubleMonoidTerm) → (P x)))))) 
  inductionB p0l p+l p1l p*l 0L = p0l  
  inductionB p0l p+l p1l p*l (+L x1 x2) = (p+l _ _ (inductionB p0l p+l p1l p*l x1) (inductionB p0l p+l p1l p*l x2))  
  inductionB p0l p+l p1l p*l 1L = p1l  
  inductionB p0l p+l p1l p*l (*L x1 x2) = (p*l _ _ (inductionB p0l p+l p1l p*l x1) (inductionB p0l p+l p1l p*l x2))  
  inductionCl :  {A : Set} {P : ((ClDoubleMonoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClDoubleMonoidTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 1Cl) → (( (x1 x2 : (ClDoubleMonoidTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClDoubleMonoidTerm A)) → (P x))))))) 
  inductionCl psing p0cl p+cl p1cl p*cl (sing x1) = (psing x1)  
  inductionCl psing p0cl p+cl p1cl p*cl 0Cl = p0cl  
  inductionCl psing p0cl p+cl p1cl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p0cl p+cl p1cl p*cl x1) (inductionCl psing p0cl p+cl p1cl p*cl x2))  
  inductionCl psing p0cl p+cl p1cl p*cl 1Cl = p1cl  
  inductionCl psing p0cl p+cl p1cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p0cl p+cl p1cl p*cl x1) (inductionCl psing p0cl p+cl p1cl p*cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpDoubleMonoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpDoubleMonoidTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 1OL) → (( (x1 x2 : (OpDoubleMonoidTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpDoubleMonoidTerm n)) → (P x))))))) 
  inductionOpB pv p0ol p+ol p1ol p*ol (v x1) = (pv x1)  
  inductionOpB pv p0ol p+ol p1ol p*ol 0OL = p0ol  
  inductionOpB pv p0ol p+ol p1ol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p0ol p+ol p1ol p*ol x1) (inductionOpB pv p0ol p+ol p1ol p*ol x2))  
  inductionOpB pv p0ol p+ol p1ol p*ol 1OL = p1ol  
  inductionOpB pv p0ol p+ol p1ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p0ol p+ol p1ol p*ol x1) (inductionOpB pv p0ol p+ol p1ol p*ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpDoubleMonoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpDoubleMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 1OL2) → (( (x1 x2 : (OpDoubleMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpDoubleMonoidTerm2 n A)) → (P x)))))))) 
  inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 x1) (inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 x2))  
  inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 x1) (inductionOp pv2 psing2 p0ol2 p+ol2 p1ol2 p*ol2 x2))  
  stageB :  (DoubleMonoidTerm → (Staged DoubleMonoidTerm))
  stageB 0L = (Now 0L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClDoubleMonoidTerm A) → (Staged (ClDoubleMonoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpDoubleMonoidTerm n) → (Staged (OpDoubleMonoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpDoubleMonoidTerm2 n A) → (Staged (OpDoubleMonoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 