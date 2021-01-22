
module MultMonoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultMonoid  (A : Set) : Set where 
     field  
      1ᵢ : A 
      * : (A → (A → A)) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z)))  
  
  open MultMonoid
  record Sig  (AS : Set) : Set where 
     field  
      1S : AS 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      1P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mu1 : (MultMonoid A1)) (Mu2 : (MultMonoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-1 : (hom (1ᵢ Mu1)) ≡ (1ᵢ Mu2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mu1) x1 x2)) ≡ ((* Mu2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mu1 : (MultMonoid A1)) (Mu2 : (MultMonoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-1 : (interp (1ᵢ Mu1) (1ᵢ Mu2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mu1) x1 x2) ((* Mu2) y1 y2)))))  
  
  data MultMonoidTerm   : Set where 
      1L : MultMonoidTerm 
      *L : (MultMonoidTerm → (MultMonoidTerm → MultMonoidTerm))  
      
  data ClMultMonoidTerm  (A : Set) : Set where 
      sing : (A → (ClMultMonoidTerm A)) 
      1Cl : (ClMultMonoidTerm A) 
      *Cl : ((ClMultMonoidTerm A) → ((ClMultMonoidTerm A) → (ClMultMonoidTerm A)))  
      
  data OpMultMonoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMultMonoidTerm n)) 
      1OL : (OpMultMonoidTerm n) 
      *OL : ((OpMultMonoidTerm n) → ((OpMultMonoidTerm n) → (OpMultMonoidTerm n)))  
      
  data OpMultMonoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMultMonoidTerm2 n A)) 
      sing2 : (A → (OpMultMonoidTerm2 n A)) 
      1OL2 : (OpMultMonoidTerm2 n A) 
      *OL2 : ((OpMultMonoidTerm2 n A) → ((OpMultMonoidTerm2 n A) → (OpMultMonoidTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClMultMonoidTerm A) → (ClMultMonoidTerm A)) 
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpMultMonoidTerm n) → (OpMultMonoidTerm n)) 
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpMultMonoidTerm2 n A) → (OpMultMonoidTerm2 n A)) 
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MultMonoid A) → (MultMonoidTerm → A)) 
  evalB Mu 1L = (1ᵢ Mu)  
  evalB Mu (*L x1 x2) = ((* Mu) (evalB Mu x1) (evalB Mu x2))  
  evalCl :  {A : Set} →  ((MultMonoid A) → ((ClMultMonoidTerm A) → A)) 
  evalCl Mu (sing x1) = x1  
  evalCl Mu 1Cl = (1ᵢ Mu)  
  evalCl Mu (*Cl x1 x2) = ((* Mu) (evalCl Mu x1) (evalCl Mu x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((MultMonoid A) → ((Vec A n) → ((OpMultMonoidTerm n) → A))) 
  evalOpB Mu vars (v x1) = (lookup vars x1)  
  evalOpB Mu vars 1OL = (1ᵢ Mu)  
  evalOpB Mu vars (*OL x1 x2) = ((* Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((MultMonoid A) → ((Vec A n) → ((OpMultMonoidTerm2 n A) → A))) 
  evalOp Mu vars (v2 x1) = (lookup vars x1)  
  evalOp Mu vars (sing2 x1) = x1  
  evalOp Mu vars 1OL2 = (1ᵢ Mu)  
  evalOp Mu vars (*OL2 x1 x2) = ((* Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  inductionB :  {P : (MultMonoidTerm → Set)} →  ((P 1L) → (( (x1 x2 : MultMonoidTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : MultMonoidTerm) → (P x)))) 
  inductionB p1l p*l 1L = p1l  
  inductionB p1l p*l (*L x1 x2) = (p*l _ _ (inductionB p1l p*l x1) (inductionB p1l p*l x2))  
  inductionCl :  {A : Set} {P : ((ClMultMonoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 1Cl) → (( (x1 x2 : (ClMultMonoidTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClMultMonoidTerm A)) → (P x))))) 
  inductionCl psing p1cl p*cl (sing x1) = (psing x1)  
  inductionCl psing p1cl p*cl 1Cl = p1cl  
  inductionCl psing p1cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p1cl p*cl x1) (inductionCl psing p1cl p*cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpMultMonoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 1OL) → (( (x1 x2 : (OpMultMonoidTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpMultMonoidTerm n)) → (P x))))) 
  inductionOpB pv p1ol p*ol (v x1) = (pv x1)  
  inductionOpB pv p1ol p*ol 1OL = p1ol  
  inductionOpB pv p1ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p1ol p*ol x1) (inductionOpB pv p1ol p*ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpMultMonoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 1OL2) → (( (x1 x2 : (OpMultMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpMultMonoidTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p1ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p1ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p1ol2 p*ol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p1ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p1ol2 p*ol2 x1) (inductionOp pv2 psing2 p1ol2 p*ol2 x2))  
  stageB :  (MultMonoidTerm → (Staged MultMonoidTerm))
  stageB 1L = (Now 1L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClMultMonoidTerm A) → (Staged (ClMultMonoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpMultMonoidTerm n) → (Staged (OpMultMonoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpMultMonoidTerm2 n A) → (Staged (OpMultMonoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      1T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 