
module Pointed1Magma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointed1Magma  (A : Set) (1ᵢ : A) (op : (A → (A → A))) : Set where 
    
  record Pointed1Magma  (A : Set) : Set where 
     field  
      1ᵢ : A 
      op : (A → (A → A)) 
      isPointed1Magma : (IsPointed1Magma A 1ᵢ op)  
  
  open Pointed1Magma
  record Sig  (AS : Set) : Set where 
     field  
      1S : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      1P : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (Pointed1Magma A1)) (Po2 : (Pointed1Magma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-1 : (hom (1ᵢ Po1)) ≡ (1ᵢ Po2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Po1) x1 x2)) ≡ ((op Po2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (Pointed1Magma A1)) (Po2 : (Pointed1Magma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-1 : (interp (1ᵢ Po1) (1ᵢ Po2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2)))))  
  
  data Pointed1MagmaTerm   : Set where 
      1L : Pointed1MagmaTerm 
      opL : (Pointed1MagmaTerm → (Pointed1MagmaTerm → Pointed1MagmaTerm))  
      
  data ClPointed1MagmaTerm  (A : Set) : Set where 
      sing : (A → (ClPointed1MagmaTerm A)) 
      1Cl : (ClPointed1MagmaTerm A) 
      opCl : ((ClPointed1MagmaTerm A) → ((ClPointed1MagmaTerm A) → (ClPointed1MagmaTerm A)))  
      
  data OpPointed1MagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointed1MagmaTerm n)) 
      1OL : (OpPointed1MagmaTerm n) 
      opOL : ((OpPointed1MagmaTerm n) → ((OpPointed1MagmaTerm n) → (OpPointed1MagmaTerm n)))  
      
  data OpPointed1MagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointed1MagmaTerm2 n A)) 
      sing2 : (A → (OpPointed1MagmaTerm2 n A)) 
      1OL2 : (OpPointed1MagmaTerm2 n A) 
      opOL2 : ((OpPointed1MagmaTerm2 n A) → ((OpPointed1MagmaTerm2 n A) → (OpPointed1MagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClPointed1MagmaTerm A) → (ClPointed1MagmaTerm A)) 
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpPointed1MagmaTerm n) → (OpPointed1MagmaTerm n)) 
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpPointed1MagmaTerm2 n A) → (OpPointed1MagmaTerm2 n A)) 
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Pointed1Magma A) → (Pointed1MagmaTerm → A)) 
  evalB Po 1L = (1ᵢ Po)  
  evalB Po (opL x1 x2) = ((op Po) (evalB Po x1) (evalB Po x2))  
  evalCl :  {A : Set} →  ((Pointed1Magma A) → ((ClPointed1MagmaTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po 1Cl = (1ᵢ Po)  
  evalCl Po (opCl x1 x2) = ((op Po) (evalCl Po x1) (evalCl Po x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Pointed1Magma A) → ((Vec A n) → ((OpPointed1MagmaTerm n) → A))) 
  evalOpB n Po vars (v x1) = (lookup vars x1)  
  evalOpB n Po vars 1OL = (1ᵢ Po)  
  evalOpB n Po vars (opOL x1 x2) = ((op Po) (evalOpB n Po vars x1) (evalOpB n Po vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Pointed1Magma A) → ((Vec A n) → ((OpPointed1MagmaTerm2 n A) → A))) 
  evalOp n Po vars (v2 x1) = (lookup vars x1)  
  evalOp n Po vars (sing2 x1) = x1  
  evalOp n Po vars 1OL2 = (1ᵢ Po)  
  evalOp n Po vars (opOL2 x1 x2) = ((op Po) (evalOp n Po vars x1) (evalOp n Po vars x2))  
  inductionB :  (P : (Pointed1MagmaTerm → Set)) →  ((P 1L) → (( (x1 x2 : Pointed1MagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : Pointed1MagmaTerm) → (P x)))) 
  inductionB p p1l popl 1L = p1l  
  inductionB p p1l popl (opL x1 x2) = (popl _ _ (inductionB p p1l popl x1) (inductionB p p1l popl x2))  
  inductionCl :  (A : Set) (P : ((ClPointed1MagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P 1Cl) → (( (x1 x2 : (ClPointed1MagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClPointed1MagmaTerm A)) → (P x))))) 
  inductionCl _ p psing p1cl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing p1cl popcl 1Cl = p1cl  
  inductionCl _ p psing p1cl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing p1cl popcl x1) (inductionCl _ p psing p1cl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpPointed1MagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P 1OL) → (( (x1 x2 : (OpPointed1MagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpPointed1MagmaTerm n)) → (P x))))) 
  inductionOpB _ p pv p1ol popol (v x1) = (pv x1)  
  inductionOpB _ p pv p1ol popol 1OL = p1ol  
  inductionOpB _ p pv p1ol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv p1ol popol x1) (inductionOpB _ p pv p1ol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpPointed1MagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 1OL2) → (( (x1 x2 : (OpPointed1MagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpPointed1MagmaTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p1ol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p1ol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p1ol2 popol2 1OL2 = p1ol2  
  inductionOp _ _ p pv2 psing2 p1ol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 p1ol2 popol2 x1) (inductionOp _ _ p pv2 psing2 p1ol2 popol2 x2))  
  stageB :  (Pointed1MagmaTerm → (Staged Pointed1MagmaTerm))
  stageB 1L = (Now 1L)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClPointed1MagmaTerm A) → (Staged (ClPointed1MagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpPointed1MagmaTerm n) → (Staged (OpPointed1MagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpPointed1MagmaTerm2 n A) → (Staged (OpPointed1MagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      1T : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 