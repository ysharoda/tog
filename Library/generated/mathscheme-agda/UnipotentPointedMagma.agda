
module UnipotentPointedMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record UnipotentPointedMagma  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      unipotence : ( {x : A} → (op x x) ≡ e)  
  
  open UnipotentPointedMagma
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      unipotenceP : ( {xP : (Prod A A)} → (opP xP xP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Un1 : (UnipotentPointedMagma A1)) (Un2 : (UnipotentPointedMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Un1)) ≡ (e Un2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Un1) x1 x2)) ≡ ((op Un2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Un1 : (UnipotentPointedMagma A1)) (Un2 : (UnipotentPointedMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Un1) (e Un2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Un1) x1 x2) ((op Un2) y1 y2)))))  
  
  data UnipotentPointedMagmaTerm   : Set where 
      eL : UnipotentPointedMagmaTerm 
      opL : (UnipotentPointedMagmaTerm → (UnipotentPointedMagmaTerm → UnipotentPointedMagmaTerm))  
      
  data ClUnipotentPointedMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClUnipotentPointedMagmaTerm A)) 
      eCl : (ClUnipotentPointedMagmaTerm A) 
      opCl : ((ClUnipotentPointedMagmaTerm A) → ((ClUnipotentPointedMagmaTerm A) → (ClUnipotentPointedMagmaTerm A)))  
      
  data OpUnipotentPointedMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpUnipotentPointedMagmaTerm n)) 
      eOL : (OpUnipotentPointedMagmaTerm n) 
      opOL : ((OpUnipotentPointedMagmaTerm n) → ((OpUnipotentPointedMagmaTerm n) → (OpUnipotentPointedMagmaTerm n)))  
      
  data OpUnipotentPointedMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpUnipotentPointedMagmaTerm2 n A)) 
      sing2 : (A → (OpUnipotentPointedMagmaTerm2 n A)) 
      eOL2 : (OpUnipotentPointedMagmaTerm2 n A) 
      opOL2 : ((OpUnipotentPointedMagmaTerm2 n A) → ((OpUnipotentPointedMagmaTerm2 n A) → (OpUnipotentPointedMagmaTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClUnipotentPointedMagmaTerm A) → (ClUnipotentPointedMagmaTerm A)) 
  simplifyCl eCl = eCl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpUnipotentPointedMagmaTerm n) → (OpUnipotentPointedMagmaTerm n)) 
  simplifyOpB eOL = eOL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpUnipotentPointedMagmaTerm2 n A) → (OpUnipotentPointedMagmaTerm2 n A)) 
  simplifyOp eOL2 = eOL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((UnipotentPointedMagma A) → (UnipotentPointedMagmaTerm → A)) 
  evalB Un eL = (e Un)  
  evalB Un (opL x1 x2) = ((op Un) (evalB Un x1) (evalB Un x2))  
  evalCl :  {A : Set} →  ((UnipotentPointedMagma A) → ((ClUnipotentPointedMagmaTerm A) → A)) 
  evalCl Un (sing x1) = x1  
  evalCl Un eCl = (e Un)  
  evalCl Un (opCl x1 x2) = ((op Un) (evalCl Un x1) (evalCl Un x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((UnipotentPointedMagma A) → ((Vec A n) → ((OpUnipotentPointedMagmaTerm n) → A))) 
  evalOpB Un vars (v x1) = (lookup vars x1)  
  evalOpB Un vars eOL = (e Un)  
  evalOpB Un vars (opOL x1 x2) = ((op Un) (evalOpB Un vars x1) (evalOpB Un vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((UnipotentPointedMagma A) → ((Vec A n) → ((OpUnipotentPointedMagmaTerm2 n A) → A))) 
  evalOp Un vars (v2 x1) = (lookup vars x1)  
  evalOp Un vars (sing2 x1) = x1  
  evalOp Un vars eOL2 = (e Un)  
  evalOp Un vars (opOL2 x1 x2) = ((op Un) (evalOp Un vars x1) (evalOp Un vars x2))  
  inductionB :  {P : (UnipotentPointedMagmaTerm → Set)} →  ((P eL) → (( (x1 x2 : UnipotentPointedMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : UnipotentPointedMagmaTerm) → (P x)))) 
  inductionB pel popl eL = pel  
  inductionB pel popl (opL x1 x2) = (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  inductionCl :  {A : Set} {P : ((ClUnipotentPointedMagmaTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClUnipotentPointedMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClUnipotentPointedMagmaTerm A)) → (P x))))) 
  inductionCl psing pecl popcl (sing x1) = (psing x1)  
  inductionCl psing pecl popcl eCl = pecl  
  inductionCl psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpUnipotentPointedMagmaTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpUnipotentPointedMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpUnipotentPointedMagmaTerm n)) → (P x))))) 
  inductionOpB pv peol popol (v x1) = (pv x1)  
  inductionOpB pv peol popol eOL = peol  
  inductionOpB pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpUnipotentPointedMagmaTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpUnipotentPointedMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpUnipotentPointedMagmaTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  stageB :  (UnipotentPointedMagmaTerm → (Staged UnipotentPointedMagmaTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClUnipotentPointedMagmaTerm A) → (Staged (ClUnipotentPointedMagmaTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl eCl = (Now eCl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpUnipotentPointedMagmaTerm n) → (Staged (OpUnipotentPointedMagmaTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB eOL = (Now eOL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpUnipotentPointedMagmaTerm2 n A) → (Staged (OpUnipotentPointedMagmaTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 