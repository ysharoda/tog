
module PointedUnarySystem   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedUnarySystem  (A : Set) : Set where 
     field  
      prim : (A → A) 
      e : A  
  
  open PointedUnarySystem
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      eP : (Prod A A)  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedUnarySystem A1)) (Po2 : (PointedUnarySystem A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim Po1) x1)) ≡ ((prim Po2) (hom x1))) 
      pres-e : (hom (e Po1)) ≡ (e Po2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedUnarySystem A1)) (Po2 : (PointedUnarySystem A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Po1) x1) ((prim Po2) y1)))) 
      interp-e : (interp (e Po1) (e Po2))  
  
  data PointedUnarySystemTerm   : Set where 
      primL : (PointedUnarySystemTerm → PointedUnarySystemTerm) 
      eL : PointedUnarySystemTerm  
      
  data ClPointedUnarySystemTerm  (A : Set) : Set where 
      sing : (A → (ClPointedUnarySystemTerm A)) 
      primCl : ((ClPointedUnarySystemTerm A) → (ClPointedUnarySystemTerm A)) 
      eCl : (ClPointedUnarySystemTerm A)  
      
  data OpPointedUnarySystemTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedUnarySystemTerm n)) 
      primOL : ((OpPointedUnarySystemTerm n) → (OpPointedUnarySystemTerm n)) 
      eOL : (OpPointedUnarySystemTerm n)  
      
  data OpPointedUnarySystemTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedUnarySystemTerm2 n A)) 
      sing2 : (A → (OpPointedUnarySystemTerm2 n A)) 
      primOL2 : ((OpPointedUnarySystemTerm2 n A) → (OpPointedUnarySystemTerm2 n A)) 
      eOL2 : (OpPointedUnarySystemTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClPointedUnarySystemTerm A) → (ClPointedUnarySystemTerm A)) 
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpPointedUnarySystemTerm n) → (OpPointedUnarySystemTerm n)) 
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpPointedUnarySystemTerm2 n A) → (OpPointedUnarySystemTerm2 n A)) 
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedUnarySystem A) → (PointedUnarySystemTerm → A)) 
  evalB Po (primL x1) = ((prim Po) (evalB Po x1))  
  evalB Po eL = (e Po)  
  evalCl :  {A : Set} →  ((PointedUnarySystem A) → ((ClPointedUnarySystemTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po (primCl x1) = ((prim Po) (evalCl Po x1))  
  evalCl Po eCl = (e Po)  
  evalOpB :  {A : Set} (n : Nat) →  ((PointedUnarySystem A) → ((Vec A n) → ((OpPointedUnarySystemTerm n) → A))) 
  evalOpB n Po vars (v x1) = (lookup vars x1)  
  evalOpB n Po vars (primOL x1) = ((prim Po) (evalOpB n Po vars x1))  
  evalOpB n Po vars eOL = (e Po)  
  evalOp :  {A : Set} (n : Nat) →  ((PointedUnarySystem A) → ((Vec A n) → ((OpPointedUnarySystemTerm2 n A) → A))) 
  evalOp n Po vars (v2 x1) = (lookup vars x1)  
  evalOp n Po vars (sing2 x1) = x1  
  evalOp n Po vars (primOL2 x1) = ((prim Po) (evalOp n Po vars x1))  
  evalOp n Po vars eOL2 = (e Po)  
  inductionB :  (P : (PointedUnarySystemTerm → Set)) →  (( (x1 : PointedUnarySystemTerm) → ((P x1) → (P (primL x1)))) → ((P eL) → ( (x : PointedUnarySystemTerm) → (P x)))) 
  inductionB p ppriml pel (primL x1) = (ppriml _ (inductionB p ppriml pel x1))  
  inductionB p ppriml pel eL = pel  
  inductionCl :  (A : Set) (P : ((ClPointedUnarySystemTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClPointedUnarySystemTerm A)) → ((P x1) → (P (primCl x1)))) → ((P eCl) → ( (x : (ClPointedUnarySystemTerm A)) → (P x))))) 
  inductionCl _ p psing pprimcl pecl (sing x1) = (psing x1)  
  inductionCl _ p psing pprimcl pecl (primCl x1) = (pprimcl _ (inductionCl _ p psing pprimcl pecl x1))  
  inductionCl _ p psing pprimcl pecl eCl = pecl  
  inductionOpB :  (n : Nat) (P : ((OpPointedUnarySystemTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpPointedUnarySystemTerm n)) → ((P x1) → (P (primOL x1)))) → ((P eOL) → ( (x : (OpPointedUnarySystemTerm n)) → (P x))))) 
  inductionOpB _ p pv pprimol peol (v x1) = (pv x1)  
  inductionOpB _ p pv pprimol peol (primOL x1) = (pprimol _ (inductionOpB _ p pv pprimol peol x1))  
  inductionOpB _ p pv pprimol peol eOL = peol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpPointedUnarySystemTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpPointedUnarySystemTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ((P eOL2) → ( (x : (OpPointedUnarySystemTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 pprimol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pprimol2 peol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 pprimol2 peol2 x1))  
  inductionOp _ _ p pv2 psing2 pprimol2 peol2 eOL2 = peol2  
  stageB :  (PointedUnarySystemTerm → (Staged PointedUnarySystemTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB eL = (Now eL)  
  stageCl :  (A : Set) →  ((ClPointedUnarySystemTerm A) → (Staged (ClPointedUnarySystemTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageCl _ eCl = (Now eCl)  
  stageOpB :  (n : Nat) →  ((OpPointedUnarySystemTerm n) → (Staged (OpPointedUnarySystemTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOpB _ eOL = (Now eOL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpPointedUnarySystemTerm2 n A) → (Staged (OpPointedUnarySystemTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  stageOp _ _ eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      eT : (Repr A)  
  
 