
module PointedTimesZeroMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointedTimesZeroMagma  (A : Set) (0ᵢ : A) (* : (A → (A → A))) : Set where 
    
  record PointedTimesZeroMagma  (A : Set) : Set where 
     field  
      0ᵢ : A 
      * : (A → (A → A)) 
      isPointedTimesZeroMagma : (IsPointedTimesZeroMagma A 0ᵢ (*))  
  
  open PointedTimesZeroMagma
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedTimesZeroMagma A1)) (Po2 : (PointedTimesZeroMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Po1)) ≡ (0ᵢ Po2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Po1) x1 x2)) ≡ ((* Po2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedTimesZeroMagma A1)) (Po2 : (PointedTimesZeroMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Po1) (0ᵢ Po2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Po1) x1 x2) ((* Po2) y1 y2)))))  
  
  data PointedTimesZeroMagmaTerm   : Set where 
      0L : PointedTimesZeroMagmaTerm 
      *L : (PointedTimesZeroMagmaTerm → (PointedTimesZeroMagmaTerm → PointedTimesZeroMagmaTerm))  
      
  data ClPointedTimesZeroMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClPointedTimesZeroMagmaTerm A)) 
      0Cl : (ClPointedTimesZeroMagmaTerm A) 
      *Cl : ((ClPointedTimesZeroMagmaTerm A) → ((ClPointedTimesZeroMagmaTerm A) → (ClPointedTimesZeroMagmaTerm A)))  
      
  data OpPointedTimesZeroMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedTimesZeroMagmaTerm n)) 
      0OL : (OpPointedTimesZeroMagmaTerm n) 
      *OL : ((OpPointedTimesZeroMagmaTerm n) → ((OpPointedTimesZeroMagmaTerm n) → (OpPointedTimesZeroMagmaTerm n)))  
      
  data OpPointedTimesZeroMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedTimesZeroMagmaTerm2 n A)) 
      sing2 : (A → (OpPointedTimesZeroMagmaTerm2 n A)) 
      0OL2 : (OpPointedTimesZeroMagmaTerm2 n A) 
      *OL2 : ((OpPointedTimesZeroMagmaTerm2 n A) → ((OpPointedTimesZeroMagmaTerm2 n A) → (OpPointedTimesZeroMagmaTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClPointedTimesZeroMagmaTerm A) → (ClPointedTimesZeroMagmaTerm A)) 
  simplifyCl 0Cl = 0Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPointedTimesZeroMagmaTerm n) → (OpPointedTimesZeroMagmaTerm n)) 
  simplifyOpB 0OL = 0OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPointedTimesZeroMagmaTerm2 n A) → (OpPointedTimesZeroMagmaTerm2 n A)) 
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedTimesZeroMagma A) → (PointedTimesZeroMagmaTerm → A)) 
  evalB Po 0L = (0ᵢ Po)  
  evalB Po (*L x1 x2) = ((* Po) (evalB Po x1) (evalB Po x2))  
  evalCl :  {A : Set} →  ((PointedTimesZeroMagma A) → ((ClPointedTimesZeroMagmaTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po 0Cl = (0ᵢ Po)  
  evalCl Po (*Cl x1 x2) = ((* Po) (evalCl Po x1) (evalCl Po x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((PointedTimesZeroMagma A) → ((Vec A n) → ((OpPointedTimesZeroMagmaTerm n) → A))) 
  evalOpB Po vars (v x1) = (lookup vars x1)  
  evalOpB Po vars 0OL = (0ᵢ Po)  
  evalOpB Po vars (*OL x1 x2) = ((* Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((PointedTimesZeroMagma A) → ((Vec A n) → ((OpPointedTimesZeroMagmaTerm2 n A) → A))) 
  evalOp Po vars (v2 x1) = (lookup vars x1)  
  evalOp Po vars (sing2 x1) = x1  
  evalOp Po vars 0OL2 = (0ᵢ Po)  
  evalOp Po vars (*OL2 x1 x2) = ((* Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  inductionB :  {P : (PointedTimesZeroMagmaTerm → Set)} →  ((P 0L) → (( (x1 x2 : PointedTimesZeroMagmaTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : PointedTimesZeroMagmaTerm) → (P x)))) 
  inductionB p0l p*l 0L = p0l  
  inductionB p0l p*l (*L x1 x2) = (p*l _ _ (inductionB p0l p*l x1) (inductionB p0l p*l x2))  
  inductionCl :  {A : Set} {P : ((ClPointedTimesZeroMagmaTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClPointedTimesZeroMagmaTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClPointedTimesZeroMagmaTerm A)) → (P x))))) 
  inductionCl psing p0cl p*cl (sing x1) = (psing x1)  
  inductionCl psing p0cl p*cl 0Cl = p0cl  
  inductionCl psing p0cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p0cl p*cl x1) (inductionCl psing p0cl p*cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpPointedTimesZeroMagmaTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpPointedTimesZeroMagmaTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpPointedTimesZeroMagmaTerm n)) → (P x))))) 
  inductionOpB pv p0ol p*ol (v x1) = (pv x1)  
  inductionOpB pv p0ol p*ol 0OL = p0ol  
  inductionOpB pv p0ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p0ol p*ol x1) (inductionOpB pv p0ol p*ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPointedTimesZeroMagmaTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpPointedTimesZeroMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpPointedTimesZeroMagmaTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p0ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 p*ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p0ol2 p*ol2 x1) (inductionOp pv2 psing2 p0ol2 p*ol2 x2))  
  stageB :  (PointedTimesZeroMagmaTerm → (Staged PointedTimesZeroMagmaTerm))
  stageB 0L = (Now 0L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClPointedTimesZeroMagmaTerm A) → (Staged (ClPointedTimesZeroMagmaTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpPointedTimesZeroMagmaTerm n) → (Staged (OpPointedTimesZeroMagmaTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpPointedTimesZeroMagmaTerm2 n A) → (Staged (OpPointedTimesZeroMagmaTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 