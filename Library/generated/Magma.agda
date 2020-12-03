
 module Magma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Magma (A : Set) : Set where
    constructor MagmaC
    field
      op : A → A → A 
  
  open Magma
  record Sig (AS : Set) : Set where
    constructor SigSigC
    field
      opS : AS → AS → AS 
  
  record Product (A : Set) : Set where
    constructor ProductC
    field
      opP : (Prod A A) → (Prod A A) → (Prod A A) 
  
  record Hom {A1 : Set} {A2 : Set} (Ma1 : (Magma A1)) (Ma2 : (Magma A2)) : Set where
    constructor HomC
    field
      hom : A1 → A2
      pres-op : ({x1 x2 : A1} → (hom ((op Ma1) x1 x2)) ≡ ((op Ma2) (hom x1) (hom x2))) 
  
  record RelInterp {A1 : Set} {A2 : Set} (Ma1 : (Magma A1)) (Ma2 : (Magma A2)) : Set₁ where
    constructor RelInterpC
    field
      interp : A1 → A2 → Set
      interp-op : ({x1 x2 : A1} {y1 y2 : A2} → (interp x1 y1) → (interp x2 y2) → (interp ((op Ma1) x1 x2) ((op Ma2) y1 y2))) 
  
  data MagmaTerm  : Set where
    opL : MagmaTerm → MagmaTerm → MagmaTerm 
  
  data ClMagmaTerm (A : Set) : Set where
    sing : A → (ClMagmaTerm A)
    opCl : (ClMagmaTerm A) → (ClMagmaTerm A) → (ClMagmaTerm A) 
  
  data OpMagmaTerm (n : Nat) : Set where
    v : (Fin n) → (OpMagmaTerm n)
    opOL : (OpMagmaTerm n) → (OpMagmaTerm n) → (OpMagmaTerm n) 
  
  data OpMagmaTerm2 (n : Nat) (A : Set) : Set where
    v2 : (Fin n) → (OpMagmaTerm2 n A)
    sing2 : A → (OpMagmaTerm2 n A)
    opOL2 : (OpMagmaTerm2 n A) → (OpMagmaTerm2 n A) → (OpMagmaTerm2 n A) 
  
  simplifyB : MagmaTerm → MagmaTerm
  simplifyB (opL x1 x2) = (opL (simplifyB x1) (simplifyB x2))
  
  simplifyCl : ((A : Set) → (ClMagmaTerm A) → (ClMagmaTerm A))
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))
  
  simplifyCl _ (sing x1) = (sing x1)
  
  simplifyOpB : ((n : Nat) → (OpMagmaTerm n) → (OpMagmaTerm n))
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))
  
  simplifyOpB _ (v x1) = (v x1)
  
  simplifyOp : ((n : Nat) (A : Set) → (OpMagmaTerm2 n A) → (OpMagmaTerm2 n A))
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))
  
  simplifyOp _ _ (v2 x1) = (v2 x1)
  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)
  
  evalB : ({A : Set} → (Magma A) → MagmaTerm → A)
  evalB Ma (opL x1 x2) = ((op Ma) (evalB Ma x1) (evalB Ma x2))
  
  evalCl : ({A : Set} → (Magma A) → (ClMagmaTerm A) → A)
  evalCl Ma (sing x1) = x1
  
  evalCl Ma (opCl x1 x2) = ((op Ma) (evalCl Ma x1) (evalCl Ma x2))
  
  evalOpB : ({A : Set} (n : Nat) → (Magma A) → (Vec A n) → (OpMagmaTerm n) → A)
  evalOpB n Ma vars (v x1) = (lookup vars x1)
  
  evalOpB n Ma vars (opOL x1 x2) = ((op Ma) (evalOpB n Ma vars x1) (evalOpB n Ma vars x2))
  
  evalOp : ({A : Set} (n : Nat) → (Magma A) → (Vec A n) → (OpMagmaTerm2 n A) → A)
  evalOp n Ma vars (v2 x1) = (lookup vars x1)
  
  evalOp n Ma vars (sing2 x1) = x1
  
  evalOp n Ma vars (opOL2 x1 x2) = ((op Ma) (evalOp n Ma vars x1) (evalOp n Ma vars x2))
  
  inductionB : ((P : MagmaTerm → Set) → ((x1 x2 : MagmaTerm) → (P x1) → (P x2) → (P (opL x1 x2))) → ((x : MagmaTerm) → (P x)))
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))
  
  inductionCl : ((A : Set) (P : (ClMagmaTerm A) → Set) → ((x1 : A) → (P (sing x1))) → ((x1 x2 : (ClMagmaTerm A)) → (P x1) → (P x2) → (P (opCl x1 x2))) → ((x : (ClMagmaTerm A)) → (P x)))
  inductionCl _ p psing popcl (sing x1) = (psing x1)
  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))
  
  inductionOpB : ((n : Nat) (P : (OpMagmaTerm n) → Set) → ((fin : (Fin n)) → (P (v fin))) → ((x1 x2 : (OpMagmaTerm n)) → (P x1) → (P x2) → (P (opOL x1 x2))) → ((x : (OpMagmaTerm n)) → (P x)))
  inductionOpB _ p pv popol (v x1) = (pv x1)
  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))
  
  inductionOp : ((n : Nat) (A : Set) (P : (OpMagmaTerm2 n A) → Set) → ((fin : (Fin n)) → (P (v2 fin))) → ((x1 : A) → (P (sing2 x1))) → ((x1 x2 : (OpMagmaTerm2 n A)) → (P x1) → (P x2) → (P (opOL2 x1 x2))) → ((x : (OpMagmaTerm2 n A)) → (P x)))
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)
  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)
  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))
  
  opL' : ( MagmaTerm → MagmaTerm → MagmaTerm)
  opL' x1 x2 = (opL x1 x2)
  
  stageB : MagmaTerm → (Staged MagmaTerm)
  stageB (opL x1 x2) = (stage2 opL' (codeLift2 opL') (stageB x1) (stageB x2))
  
  opCl' : ({A : Set} → (ClMagmaTerm A) → (ClMagmaTerm A) → (ClMagmaTerm A))
  opCl' x1 x2 = (opCl x1 x2)
  
  stageCl : ((A : Set) → (ClMagmaTerm A) → (Staged (ClMagmaTerm A)))
  stageCl _ (sing x1) = (Now (sing x1))
  
  stageCl _ (opCl x1 x2) = (stage2 opCl' (codeLift2 opCl') ((stageCl _) x1) ((stageCl _) x2))
  
  opOL' : ({n : Nat} → (OpMagmaTerm n) → (OpMagmaTerm n) → (OpMagmaTerm n))
  opOL' x1 x2 = (opOL x1 x2)
  
  stageOpB : ((n : Nat) → (OpMagmaTerm n) → (Staged (OpMagmaTerm n)))
  stageOpB _ (v x1) = (const (code (v x1)))
  
  stageOpB _ (opOL x1 x2) = (stage2 opOL' (codeLift2 opOL') ((stageOpB _) x1) ((stageOpB _) x2))
  
  opOL2' : ({n : Nat} {A : Set} → (OpMagmaTerm2 n A) → (OpMagmaTerm2 n A) → (OpMagmaTerm2 n A))
  opOL2' x1 x2 = (opOL2 x1 x2)
  
  stageOp : ((n : Nat) (A : Set) → (OpMagmaTerm2 n A) → (Staged (OpMagmaTerm2 n A)))
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))
  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))
  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2' (codeLift2 opOL2') ((stageOp _ _) x1) ((stageOp _ _) x2))
  
  record Tagless (A : Set) (Repr : Set → Set) : Set where
    constructor tagless
    field
      opT : (Repr A) → (Repr A) → (Repr A) 
   
