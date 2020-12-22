
module PointedSteinerMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointedSteinerMagma  (A : Set) (op : (A → (A → A))) (e : A) : Set where 
     field  
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x)) 
      antiAbsorbent : ( {x y : A} → (op x (op x y)) ≡ y)  
  
  record PointedSteinerMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      isPointedSteinerMagma : (IsPointedSteinerMagma A op e)  
  
  open PointedSteinerMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP)) 
      antiAbsorbentP : ( {xP yP : (Prod A A)} → (opP xP (opP xP yP)) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Po1 : (PointedSteinerMagma A1)) (Po2 : (PointedSteinerMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Po1) x1 x2)) ≡ ((op Po2) (hom x1) (hom x2))) 
      pres-e : (hom (e Po1)) ≡ (e Po2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Po1 : (PointedSteinerMagma A1)) (Po2 : (PointedSteinerMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2))))) 
      interp-e : (interp (e Po1) (e Po2))  
  
  data PointedSteinerMagmaTerm   : Set where 
      opL : (PointedSteinerMagmaTerm → (PointedSteinerMagmaTerm → PointedSteinerMagmaTerm)) 
      eL : PointedSteinerMagmaTerm  
      
  data ClPointedSteinerMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClPointedSteinerMagmaTerm A)) 
      opCl : ((ClPointedSteinerMagmaTerm A) → ((ClPointedSteinerMagmaTerm A) → (ClPointedSteinerMagmaTerm A))) 
      eCl : (ClPointedSteinerMagmaTerm A)  
      
  data OpPointedSteinerMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPointedSteinerMagmaTerm n)) 
      opOL : ((OpPointedSteinerMagmaTerm n) → ((OpPointedSteinerMagmaTerm n) → (OpPointedSteinerMagmaTerm n))) 
      eOL : (OpPointedSteinerMagmaTerm n)  
      
  data OpPointedSteinerMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPointedSteinerMagmaTerm2 n A)) 
      sing2 : (A → (OpPointedSteinerMagmaTerm2 n A)) 
      opOL2 : ((OpPointedSteinerMagmaTerm2 n A) → ((OpPointedSteinerMagmaTerm2 n A) → (OpPointedSteinerMagmaTerm2 n A))) 
      eOL2 : (OpPointedSteinerMagmaTerm2 n A)  
      
  simplifyCl :  (A : Set) →  ((ClPointedSteinerMagmaTerm A) → (ClPointedSteinerMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpPointedSteinerMagmaTerm n) → (OpPointedSteinerMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpPointedSteinerMagmaTerm2 n A) → (OpPointedSteinerMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PointedSteinerMagma A) → (PointedSteinerMagmaTerm → A)) 
  evalB Po (opL x1 x2) = ((op Po) (evalB Po x1) (evalB Po x2))  
  evalB Po eL = (e Po)  
  evalCl :  {A : Set} →  ((PointedSteinerMagma A) → ((ClPointedSteinerMagmaTerm A) → A)) 
  evalCl Po (sing x1) = x1  
  evalCl Po (opCl x1 x2) = ((op Po) (evalCl Po x1) (evalCl Po x2))  
  evalCl Po eCl = (e Po)  
  evalOpB :  {A : Set} (n : Nat) →  ((PointedSteinerMagma A) → ((Vec A n) → ((OpPointedSteinerMagmaTerm n) → A))) 
  evalOpB n Po vars (v x1) = (lookup vars x1)  
  evalOpB n Po vars (opOL x1 x2) = ((op Po) (evalOpB n Po vars x1) (evalOpB n Po vars x2))  
  evalOpB n Po vars eOL = (e Po)  
  evalOp :  {A : Set} (n : Nat) →  ((PointedSteinerMagma A) → ((Vec A n) → ((OpPointedSteinerMagmaTerm2 n A) → A))) 
  evalOp n Po vars (v2 x1) = (lookup vars x1)  
  evalOp n Po vars (sing2 x1) = x1  
  evalOp n Po vars (opOL2 x1 x2) = ((op Po) (evalOp n Po vars x1) (evalOp n Po vars x2))  
  evalOp n Po vars eOL2 = (e Po)  
  inductionB :  (P : (PointedSteinerMagmaTerm → Set)) →  (( (x1 x2 : PointedSteinerMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : PointedSteinerMagmaTerm) → (P x)))) 
  inductionB p popl pel (opL x1 x2) = (popl _ _ (inductionB p popl pel x1) (inductionB p popl pel x2))  
  inductionB p popl pel eL = pel  
  inductionCl :  (A : Set) (P : ((ClPointedSteinerMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClPointedSteinerMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClPointedSteinerMagmaTerm A)) → (P x))))) 
  inductionCl _ p psing popcl pecl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl pecl x1) (inductionCl _ p psing popcl pecl x2))  
  inductionCl _ p psing popcl pecl eCl = pecl  
  inductionOpB :  (n : Nat) (P : ((OpPointedSteinerMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpPointedSteinerMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpPointedSteinerMagmaTerm n)) → (P x))))) 
  inductionOpB _ p pv popol peol (v x1) = (pv x1)  
  inductionOpB _ p pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol peol x1) (inductionOpB _ p pv popol peol x2))  
  inductionOpB _ p pv popol peol eOL = peol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpPointedSteinerMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpPointedSteinerMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpPointedSteinerMagmaTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 peol2 x1) (inductionOp _ _ p pv2 psing2 popol2 peol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (PointedSteinerMagmaTerm → (Staged PointedSteinerMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  (A : Set) →  ((ClPointedSteinerMagmaTerm A) → (Staged (ClPointedSteinerMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ eCl = (Now eCl)  
  stageOpB :  (n : Nat) →  ((OpPointedSteinerMagmaTerm n) → (Staged (OpPointedSteinerMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ eOL = (Now eOL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpPointedSteinerMagmaTerm2 n A) → (Staged (OpPointedSteinerMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 