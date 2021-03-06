
module PointedTimesMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedTimesMagma  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      e : A  
  
  open PointedTimesMagma
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A)  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedTimesMagma A1)) (Po2 : (PointedTimesMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Po1) x1 x2)) ≡ ((* Po2) (hom x1) (hom x2))) 
      pres-e : (hom (e Po1)) ≡ (e Po2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedTimesMagma A1)) (Po2 : (PointedTimesMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Po1) x1 x2) ((* Po2) y1 y2))))) 
      interp-e : (interp (e Po1) (e Po2))  
  
  data PointedTimesMagmaTerm   : Set where 
      *L : (PointedTimesMagmaTerm → (PointedTimesMagmaTerm → PointedTimesMagmaTerm)) 
      eL : PointedTimesMagmaTerm  
      
  data ClPointedTimesMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClPointedTimesMagmaTerm A)) 
      *Cl : ((ClPointedTimesMagmaTerm A) → ((ClPointedTimesMagmaTerm A) → (ClPointedTimesMagmaTerm A))) 
      eCl : (ClPointedTimesMagmaTerm A)  
      
  data OpPointedTimesMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedTimesMagmaTerm n)) 
      *OL : ((OpPointedTimesMagmaTerm n) → ((OpPointedTimesMagmaTerm n) → (OpPointedTimesMagmaTerm n))) 
      eOL : (OpPointedTimesMagmaTerm n)  
      
  data OpPointedTimesMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedTimesMagmaTerm2 n A)) 
      sing2 : (A → (OpPointedTimesMagmaTerm2 n A)) 
      *OL2 : ((OpPointedTimesMagmaTerm2 n A) → ((OpPointedTimesMagmaTerm2 n A) → (OpPointedTimesMagmaTerm2 n A))) 
      eOL2 : (OpPointedTimesMagmaTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClPointedTimesMagmaTerm A) → (ClPointedTimesMagmaTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPointedTimesMagmaTerm n) → (OpPointedTimesMagmaTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPointedTimesMagmaTerm2 n A) → (OpPointedTimesMagmaTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedTimesMagma A) → (PointedTimesMagmaTerm → A)) 
  evalB Po (*L x1 x2) = ((* Po) (evalB Po x1) (evalB Po x2))  
  evalB Po eL = (e Po)  
  evalCl :  {A : Set} →  ((PointedTimesMagma A) → ((ClPointedTimesMagmaTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po (*Cl x1 x2) = ((* Po) (evalCl Po x1) (evalCl Po x2))  
  evalCl Po eCl = (e Po)  
  evalOpB :  {A : Set} {n : Nat} →  ((PointedTimesMagma A) → ((Vec A n) → ((OpPointedTimesMagmaTerm n) → A))) 
  evalOpB Po vars (v x1) = (lookup vars x1)  
  evalOpB Po vars (*OL x1 x2) = ((* Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  evalOpB Po vars eOL = (e Po)  
  evalOp :  {A : Set} {n : Nat} →  ((PointedTimesMagma A) → ((Vec A n) → ((OpPointedTimesMagmaTerm2 n A) → A))) 
  evalOp Po vars (v2 x1) = (lookup vars x1)  
  evalOp Po vars (sing2 x1) = x1  
  evalOp Po vars (*OL2 x1 x2) = ((* Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  evalOp Po vars eOL2 = (e Po)  
  inductionB :  {P : (PointedTimesMagmaTerm → Set)} →  (( (x1 x2 : PointedTimesMagmaTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ((P eL) → ( (x : PointedTimesMagmaTerm) → (P x)))) 
  inductionB p*l pel (*L x1 x2) = (p*l _ _ (inductionB p*l pel x1) (inductionB p*l pel x2))  
  inductionB p*l pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClPointedTimesMagmaTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClPointedTimesMagmaTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ((P eCl) → ( (x : (ClPointedTimesMagmaTerm A)) → (P x))))) 
  inductionCl psing p*cl pecl (sing x1) = (psing x1)  
  inductionCl psing p*cl pecl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl pecl x1) (inductionCl psing p*cl pecl x2))  
  inductionCl psing p*cl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpPointedTimesMagmaTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpPointedTimesMagmaTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ((P eOL) → ( (x : (OpPointedTimesMagmaTerm n)) → (P x))))) 
  inductionOpB pv p*ol peol (v x1) = (pv x1)  
  inductionOpB pv p*ol peol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol peol x1) (inductionOpB pv p*ol peol x2))  
  inductionOpB pv p*ol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPointedTimesMagmaTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpPointedTimesMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ((P eOL2) → ( (x : (OpPointedTimesMagmaTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 peol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 peol2 x1) (inductionOp pv2 psing2 p*ol2 peol2 x2))  
  inductionOp pv2 psing2 p*ol2 peol2 eOL2 = peol2  
  stageB :  (PointedTimesMagmaTerm → (Staged PointedTimesMagmaTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClPointedTimesMagmaTerm A) → (Staged (ClPointedTimesMagmaTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpPointedTimesMagmaTerm n) → (Staged (OpPointedTimesMagmaTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpPointedTimesMagmaTerm2 n A) → (Staged (OpPointedTimesMagmaTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 