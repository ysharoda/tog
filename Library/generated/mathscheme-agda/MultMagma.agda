
module MultMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultMagma  (A : Set) : Set where 
     field  
      * : (A → (A → A))  
  
  open MultMagma
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mu1 : (MultMagma A1)) (Mu2 : (MultMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mu1) x1 x2)) ≡ ((* Mu2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mu1 : (MultMagma A1)) (Mu2 : (MultMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mu1) x1 x2) ((* Mu2) y1 y2)))))  
  
  data MultMagmaTerm   : Set where 
      *L : (MultMagmaTerm → (MultMagmaTerm → MultMagmaTerm))  
      
  data ClMultMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClMultMagmaTerm A)) 
      *Cl : ((ClMultMagmaTerm A) → ((ClMultMagmaTerm A) → (ClMultMagmaTerm A)))  
      
  data OpMultMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMultMagmaTerm n)) 
      *OL : ((OpMultMagmaTerm n) → ((OpMultMagmaTerm n) → (OpMultMagmaTerm n)))  
      
  data OpMultMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMultMagmaTerm2 n A)) 
      sing2 : (A → (OpMultMagmaTerm2 n A)) 
      *OL2 : ((OpMultMagmaTerm2 n A) → ((OpMultMagmaTerm2 n A) → (OpMultMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMultMagmaTerm A) → (ClMultMagmaTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMultMagmaTerm n) → (OpMultMagmaTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMultMagmaTerm2 n A) → (OpMultMagmaTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MultMagma A) → (MultMagmaTerm → A)) 
  evalB Mu (*L x1 x2) = ((* Mu) (evalB Mu x1) (evalB Mu x2))  
  evalCl :  {A : Set} →  ((MultMagma A) → ((ClMultMagmaTerm A) → A)) 
  evalCl Mu (sing x1) = x1  
  evalCl Mu (*Cl x1 x2) = ((* Mu) (evalCl Mu x1) (evalCl Mu x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MultMagma A) → ((Vec A n) → ((OpMultMagmaTerm n) → A))) 
  evalOpB n Mu vars (v x1) = (lookup vars x1)  
  evalOpB n Mu vars (*OL x1 x2) = ((* Mu) (evalOpB n Mu vars x1) (evalOpB n Mu vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MultMagma A) → ((Vec A n) → ((OpMultMagmaTerm2 n A) → A))) 
  evalOp n Mu vars (v2 x1) = (lookup vars x1)  
  evalOp n Mu vars (sing2 x1) = x1  
  evalOp n Mu vars (*OL2 x1 x2) = ((* Mu) (evalOp n Mu vars x1) (evalOp n Mu vars x2))  
  inductionB :  (P : (MultMagmaTerm → Set)) →  (( (x1 x2 : MultMagmaTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : MultMagmaTerm) → (P x))) 
  inductionB p p*l (*L x1 x2) = (p*l _ _ (inductionB p p*l x1) (inductionB p p*l x2))  
  inductionCl :  (A : Set) (P : ((ClMultMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMultMagmaTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClMultMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl x1) (inductionCl _ p psing p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMultMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMultMagmaTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpMultMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol x1) (inductionOpB _ p pv p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMultMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMultMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpMultMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 x2))  
  stageB :  (MultMagmaTerm → (Staged MultMagmaTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMultMagmaTerm A) → (Staged (ClMultMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMultMagmaTerm n) → (Staged (OpMultMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMultMagmaTerm2 n A) → (Staged (OpMultMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 