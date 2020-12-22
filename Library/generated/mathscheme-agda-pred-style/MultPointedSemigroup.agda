
module MultPointedSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMultPointedSemigroup  (A : Set) (1ᵢ : A) (* : (A → (A → A))) : Set where 
     field  
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z)))  
  
  record MultPointedSemigroup  (A : Set) : Set where 
     field  
      1ᵢ : A 
      * : (A → (A → A)) 
      isMultPointedSemigroup : (IsMultPointedSemigroup A 1ᵢ (*))  
  
  open MultPointedSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      1S : AS 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      1P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mu1 : (MultPointedSemigroup A1)) (Mu2 : (MultPointedSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-1 : (hom (1ᵢ Mu1)) ≡ (1ᵢ Mu2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mu1) x1 x2)) ≡ ((* Mu2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mu1 : (MultPointedSemigroup A1)) (Mu2 : (MultPointedSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-1 : (interp (1ᵢ Mu1) (1ᵢ Mu2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mu1) x1 x2) ((* Mu2) y1 y2)))))  
  
  data MultPointedSemigroupTerm   : Set where 
      1L : MultPointedSemigroupTerm 
      *L : (MultPointedSemigroupTerm → (MultPointedSemigroupTerm → MultPointedSemigroupTerm))  
      
  data ClMultPointedSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClMultPointedSemigroupTerm A)) 
      1Cl : (ClMultPointedSemigroupTerm A) 
      *Cl : ((ClMultPointedSemigroupTerm A) → ((ClMultPointedSemigroupTerm A) → (ClMultPointedSemigroupTerm A)))  
      
  data OpMultPointedSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMultPointedSemigroupTerm n)) 
      1OL : (OpMultPointedSemigroupTerm n) 
      *OL : ((OpMultPointedSemigroupTerm n) → ((OpMultPointedSemigroupTerm n) → (OpMultPointedSemigroupTerm n)))  
      
  data OpMultPointedSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMultPointedSemigroupTerm2 n A)) 
      sing2 : (A → (OpMultPointedSemigroupTerm2 n A)) 
      1OL2 : (OpMultPointedSemigroupTerm2 n A) 
      *OL2 : ((OpMultPointedSemigroupTerm2 n A) → ((OpMultPointedSemigroupTerm2 n A) → (OpMultPointedSemigroupTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMultPointedSemigroupTerm A) → (ClMultPointedSemigroupTerm A)) 
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMultPointedSemigroupTerm n) → (OpMultPointedSemigroupTerm n)) 
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMultPointedSemigroupTerm2 n A) → (OpMultPointedSemigroupTerm2 n A)) 
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MultPointedSemigroup A) → (MultPointedSemigroupTerm → A)) 
  evalB Mu 1L = (1ᵢ Mu)  
  evalB Mu (*L x1 x2) = ((* Mu) (evalB Mu x1) (evalB Mu x2))  
  evalCl :  {A : Set} →  ((MultPointedSemigroup A) → ((ClMultPointedSemigroupTerm A) → A)) 
  evalCl Mu (sing x1) = x1  
  evalCl Mu 1Cl = (1ᵢ Mu)  
  evalCl Mu (*Cl x1 x2) = ((* Mu) (evalCl Mu x1) (evalCl Mu x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MultPointedSemigroup A) → ((Vec A n) → ((OpMultPointedSemigroupTerm n) → A))) 
  evalOpB n Mu vars (v x1) = (lookup vars x1)  
  evalOpB n Mu vars 1OL = (1ᵢ Mu)  
  evalOpB n Mu vars (*OL x1 x2) = ((* Mu) (evalOpB n Mu vars x1) (evalOpB n Mu vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MultPointedSemigroup A) → ((Vec A n) → ((OpMultPointedSemigroupTerm2 n A) → A))) 
  evalOp n Mu vars (v2 x1) = (lookup vars x1)  
  evalOp n Mu vars (sing2 x1) = x1  
  evalOp n Mu vars 1OL2 = (1ᵢ Mu)  
  evalOp n Mu vars (*OL2 x1 x2) = ((* Mu) (evalOp n Mu vars x1) (evalOp n Mu vars x2))  
  inductionB :  (P : (MultPointedSemigroupTerm → Set)) →  ((P 1L) → (( (x1 x2 : MultPointedSemigroupTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : MultPointedSemigroupTerm) → (P x)))) 
  inductionB p p1l p*l 1L = p1l  
  inductionB p p1l p*l (*L x1 x2) = (p*l _ _ (inductionB p p1l p*l x1) (inductionB p p1l p*l x2))  
  inductionCl :  (A : Set) (P : ((ClMultPointedSemigroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P 1Cl) → (( (x1 x2 : (ClMultPointedSemigroupTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClMultPointedSemigroupTerm A)) → (P x))))) 
  inductionCl _ p psing p1cl p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p1cl p*cl 1Cl = p1cl  
  inductionCl _ p psing p1cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p1cl p*cl x1) (inductionCl _ p psing p1cl p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMultPointedSemigroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P 1OL) → (( (x1 x2 : (OpMultPointedSemigroupTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpMultPointedSemigroupTerm n)) → (P x))))) 
  inductionOpB _ p pv p1ol p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p1ol p*ol 1OL = p1ol  
  inductionOpB _ p pv p1ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p1ol p*ol x1) (inductionOpB _ p pv p1ol p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMultPointedSemigroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 1OL2) → (( (x1 x2 : (OpMultPointedSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpMultPointedSemigroupTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p1ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p1ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p1ol2 p*ol2 1OL2 = p1ol2  
  inductionOp _ _ p pv2 psing2 p1ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p1ol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p1ol2 p*ol2 x2))  
  stageB :  (MultPointedSemigroupTerm → (Staged MultPointedSemigroupTerm))
  stageB 1L = (Now 1L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMultPointedSemigroupTerm A) → (Staged (ClMultPointedSemigroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMultPointedSemigroupTerm n) → (Staged (OpMultPointedSemigroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMultPointedSemigroupTerm2 n A) → (Staged (OpMultPointedSemigroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      1T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 