
 module PointedMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedMagma (A : Set) : Set where
    constructor PointedMagmaC
    field
      e : A
      op : A → A → A 
  
  open PointedMagma
  record Sig (AS : Set) : Set where
    constructor SigSigC
    field
      eS : AS
      opS : AS → AS → AS 
  
  record Product (A : Set) : Set where
    constructor ProductC
    field
      eP : (Prod A A)
      opP : (Prod A A) → (Prod A A) → (Prod A A) 
  
  record Hom {A1 : Set} {A2 : Set} (Po1 : (PointedMagma A1)) (Po2 : (PointedMagma A2)) : Set where
    constructor HomC
    field
      hom : A1 → A2
      pres-e : (hom (e Po1)) ≡ (e Po2)
      pres-op : ({x1 x2 : A1} → (hom ((op Po1) x1 x2)) ≡ ((op Po2) (hom x1) (hom x2))) 
  
  record RelInterp {A1 : Set} {A2 : Set} (Po1 : (PointedMagma A1)) (Po2 : (PointedMagma A2)) : Set₁ where
    constructor RelInterpC
    field
      interp : A1 → A2 → Set
      interp-e : (interp (e Po1) (e Po2))
      interp-op : ({x1 x2 : A1} {y1 y2 : A2} → (interp x1 y1) → (interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2))) 
  
  data PointedMagmaTerm  : Set where
    eL : PointedMagmaTerm
    opL : PointedMagmaTerm → PointedMagmaTerm → PointedMagmaTerm 
  
  data ClPointedMagmaTerm (A : Set) : Set where
    sing : A → (ClPointedMagmaTerm A)
    eCl : (ClPointedMagmaTerm A)
    opCl : (ClPointedMagmaTerm A) → (ClPointedMagmaTerm A) → (ClPointedMagmaTerm A) 
  
  data OpPointedMagmaTerm (n : Nat) : Set where
    v : (Fin n) → (OpPointedMagmaTerm n)
    eOL : (OpPointedMagmaTerm n)
    opOL : (OpPointedMagmaTerm n) → (OpPointedMagmaTerm n) → (OpPointedMagmaTerm n) 
  
  data OpPointedMagmaTerm2 (n : Nat) (A : Set) : Set where
    v2 : (Fin n) → (OpPointedMagmaTerm2 n A)
    sing2 : A → (OpPointedMagmaTerm2 n A)
    eOL2 : (OpPointedMagmaTerm2 n A)
    opOL2 : (OpPointedMagmaTerm2 n A) → (OpPointedMagmaTerm2 n A) → (OpPointedMagmaTerm2 n A) 
  
  simplifyB : PointedMagmaTerm → PointedMagmaTerm
  simplifyB eL = eL
  
  simplifyB (opL x1 x2) = (opL (simplifyB x1) (simplifyB x2))
  
  simplifyCl : ((A : Set) → (ClPointedMagmaTerm A) → (ClPointedMagmaTerm A))
  simplifyCl _ eCl = eCl
  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))
  
  simplifyCl _ (sing x1) = (sing x1)
  
  simplifyOpB : ((n : Nat) → (OpPointedMagmaTerm n) → (OpPointedMagmaTerm n))
  simplifyOpB _ eOL = eOL
  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))
  
  simplifyOpB _ (v x1) = (v x1)
  
  simplifyOp : ((n : Nat) (A : Set) → (OpPointedMagmaTerm2 n A) → (OpPointedMagmaTerm2 n A))
  simplifyOp _ _ eOL2 = eOL2
  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))
  
  simplifyOp _ _ (v2 x1) = (v2 x1)
  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)
  
  evalB : ({A : Set} → (PointedMagma A) → PointedMagmaTerm → A)
  evalB Po eL = (e Po)
  
  evalB Po (opL x1 x2) = ((op Po) (evalB Po x1) (evalB Po x2))
  
  evalCl : ({A : Set} → (PointedMagma A) → (ClPointedMagmaTerm A) → A)
  evalCl Po (sing x1) = x1
  
  evalCl Po eCl = (e Po)
  
  evalCl Po (opCl x1 x2) = ((op Po) (evalCl Po x1) (evalCl Po x2))
  
  evalOpB : ({A : Set} (n : Nat) → (PointedMagma A) → (Vec A n) → (OpPointedMagmaTerm n) → A)
  evalOpB n Po vars (v x1) = (lookup vars x1)
  
  evalOpB n Po vars eOL = (e Po)
  
  evalOpB n Po vars (opOL x1 x2) = ((op Po) (evalOpB n Po vars x1) (evalOpB n Po vars x2))
  
  evalOp : ({A : Set} (n : Nat) → (PointedMagma A) → (Vec A n) → (OpPointedMagmaTerm2 n A) → A)
  evalOp n Po vars (v2 x1) = (lookup vars x1)
  
  evalOp n Po vars (sing2 x1) = x1
  
  evalOp n Po vars eOL2 = (e Po)
  
  evalOp n Po vars (opOL2 x1 x2) = ((op Po) (evalOp n Po vars x1) (evalOp n Po vars x2))
  
  inductionB : ((P : PointedMagmaTerm → Set) → (P eL) → ((x1 x2 : PointedMagmaTerm) → (P x1) → (P x2) → (P (opL x1 x2))) → ((x : PointedMagmaTerm) → (P x)))
  inductionB p pel popl eL = pel
  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))
  
  inductionCl : ((A : Set) (P : (ClPointedMagmaTerm A) → Set) → ((x1 : A) → (P (sing x1))) → (P eCl) → ((x1 x2 : (ClPointedMagmaTerm A)) → (P x1) → (P x2) → (P (opCl x1 x2))) → ((x : (ClPointedMagmaTerm A)) → (P x)))
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)
  
  inductionCl _ p psing pecl popcl eCl = pecl
  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))
  
  inductionOpB : ((n : Nat) (P : (OpPointedMagmaTerm n) → Set) → ((fin : (Fin n)) → (P (v fin))) → (P eOL) → ((x1 x2 : (OpPointedMagmaTerm n)) → (P x1) → (P x2) → (P (opOL x1 x2))) → ((x : (OpPointedMagmaTerm n)) → (P x)))
  inductionOpB _ p pv peol popol (v x1) = (pv x1)
  
  inductionOpB _ p pv peol popol eOL = peol
  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))
  
  inductionOp : ((n : Nat) (A : Set) (P : (OpPointedMagmaTerm2 n A) → Set) → ((fin : (Fin n)) → (P (v2 fin))) → ((x1 : A) → (P (sing2 x1))) → (P eOL2) → ((x1 x2 : (OpPointedMagmaTerm2 n A)) → (P x1) → (P x2) → (P (opOL2 x1 x2))) → ((x : (OpPointedMagmaTerm2 n A)) → (P x)))
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))
  
  eL' : ( PointedMagmaTerm)
  eL'  = eL
  
  opL' : ( PointedMagmaTerm → PointedMagmaTerm → PointedMagmaTerm)
  opL' x1 x2 = (opL x1 x2)
  
  stageB : PointedMagmaTerm → (Staged PointedMagmaTerm)
  stageB eL = (Now eL)
  
  stageB (opL x1 x2) = (stage2 opL' (codeLift2 opL') (stageB x1) (stageB x2))
  
  eCl' : ({A : Set} → (ClPointedMagmaTerm A))
  eCl'  = eCl
  
  opCl' : ({A : Set} → (ClPointedMagmaTerm A) → (ClPointedMagmaTerm A) → (ClPointedMagmaTerm A))
  opCl' x1 x2 = (opCl x1 x2)
  
  stageCl : ((A : Set) → (ClPointedMagmaTerm A) → (Staged (ClPointedMagmaTerm A)))
  stageCl _ (sing x1) = (Now (sing x1))
  
  stageCl _ eCl = (Now eCl)
  
  stageCl _ (opCl x1 x2) = (stage2 opCl' (codeLift2 opCl') ((stageCl _) x1) ((stageCl _) x2))
  
  eOL' : ({n : Nat} → (OpPointedMagmaTerm n))
  eOL'  = eOL
  
  opOL' : ({n : Nat} → (OpPointedMagmaTerm n) → (OpPointedMagmaTerm n) → (OpPointedMagmaTerm n))
  opOL' x1 x2 = (opOL x1 x2)
  
  stageOpB : ((n : Nat) → (OpPointedMagmaTerm n) → (Staged (OpPointedMagmaTerm n)))
  stageOpB _ (v x1) = (const (code (v x1)))
  
  stageOpB _ eOL = (Now eOL)
  
  stageOpB _ (opOL x1 x2) = (stage2 opOL' (codeLift2 opOL') ((stageOpB _) x1) ((stageOpB _) x2))
  
  eOL2' : ({n : Nat} {A : Set} → (OpPointedMagmaTerm2 n A))
  eOL2'  = eOL2
  
  opOL2' : ({n : Nat} {A : Set} → (OpPointedMagmaTerm2 n A) → (OpPointedMagmaTerm2 n A) → (OpPointedMagmaTerm2 n A))
  opOL2' x1 x2 = (opOL2 x1 x2)
  
  stageOp : ((n : Nat) (A : Set) → (OpPointedMagmaTerm2 n A) → (Staged (OpPointedMagmaTerm2 n A)))
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))
  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))
  
  stageOp _ _ eOL2 = (Now eOL2)
  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2' (codeLift2 opOL2') ((stageOp _ _) x1) ((stageOp _ _) x2))
  
  record Tagless (A : Set) (Repr : Set → Set) : Set where
    constructor tagless
    field
      eT : (Repr A)
      opT : (Repr A) → (Repr A) → (Repr A) 
   
