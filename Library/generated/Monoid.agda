
 module Monoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Monoid (A : Set) : Set where
    constructor MonoidC
    field
      e : A
      op : A → A → A
      lunit_e : ({x : A} → (op e x) ≡ x)
      runit_e : ({x : A} → (op x e) ≡ x)
      associative_op : ({x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
  
  open Monoid
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
      lunit_eP : ({xP : (Prod A A)} → (opP eP xP) ≡ xP)
      runit_eP : ({xP : (Prod A A)} → (opP xP eP) ≡ xP)
      associative_opP : ({xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
  
  record Hom {A1 : Set} {A2 : Set} (Mo1 : (Monoid A1)) (Mo2 : (Monoid A2)) : Set where
    constructor HomC
    field
      hom : A1 → A2
      pres-e : (hom (e Mo1)) ≡ (e Mo2)
      pres-op : ({x1 x2 : A1} → (hom ((op Mo1) x1 x2)) ≡ ((op Mo2) (hom x1) (hom x2))) 
  
  record RelInterp {A1 : Set} {A2 : Set} (Mo1 : (Monoid A1)) (Mo2 : (Monoid A2)) : Set₁ where
    constructor RelInterpC
    field
      interp : A1 → A2 → Set
      interp-e : (interp (e Mo1) (e Mo2))
      interp-op : ({x1 x2 : A1} {y1 y2 : A2} → (interp x1 y1) → (interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2))) 
  
  data MonoidTerm  : Set where
    eL : MonoidTerm
    opL : MonoidTerm → MonoidTerm → MonoidTerm 
  
  data ClMonoidTerm (A : Set) : Set where
    sing : A → (ClMonoidTerm A)
    eCl : (ClMonoidTerm A)
    opCl : (ClMonoidTerm A) → (ClMonoidTerm A) → (ClMonoidTerm A) 
  
  data OpMonoidTerm (n : Nat) : Set where
    v : (Fin n) → (OpMonoidTerm n)
    eOL : (OpMonoidTerm n)
    opOL : (OpMonoidTerm n) → (OpMonoidTerm n) → (OpMonoidTerm n) 
  
  data OpMonoidTerm2 (n : Nat) (A : Set) : Set where
    v2 : (Fin n) → (OpMonoidTerm2 n A)
    sing2 : A → (OpMonoidTerm2 n A)
    eOL2 : (OpMonoidTerm2 n A)
    opOL2 : (OpMonoidTerm2 n A) → (OpMonoidTerm2 n A) → (OpMonoidTerm2 n A) 
  
  simplifyB : MonoidTerm → MonoidTerm
  simplifyB (opL eL x) = x
  
  simplifyB (opL x eL) = x
  
  simplifyB eL = eL
  
  simplifyB (opL x1 x2) = (opL (simplifyB x1) (simplifyB x2))
  
  simplifyCl : ((A : Set) → (ClMonoidTerm A) → (ClMonoidTerm A))
  simplifyCl _ (opCl eCl x) = x
  
  simplifyCl _ (opCl x eCl) = x
  
  simplifyCl _ eCl = eCl
  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))
  
  simplifyCl _ (sing x1) = (sing x1)
  
  simplifyOpB : ((n : Nat) → (OpMonoidTerm n) → (OpMonoidTerm n))
  simplifyOpB _ (opOL eOL x) = x
  
  simplifyOpB _ (opOL x eOL) = x
  
  simplifyOpB _ eOL = eOL
  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))
  
  simplifyOpB _ (v x1) = (v x1)
  
  simplifyOp : ((n : Nat) (A : Set) → (OpMonoidTerm2 n A) → (OpMonoidTerm2 n A))
  simplifyOp _ _ (opOL2 eOL2 x) = x
  
  simplifyOp _ _ (opOL2 x eOL2) = x
  
  simplifyOp _ _ eOL2 = eOL2
  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))
  
  simplifyOp _ _ (v2 x1) = (v2 x1)
  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)
  
  evalB : ({A : Set} → (Monoid A) → MonoidTerm → A)
  evalB Mo eL = (e Mo)
  
  evalB Mo (opL x1 x2) = ((op Mo) (evalB Mo x1) (evalB Mo x2))
  
  evalCl : ({A : Set} → (Monoid A) → (ClMonoidTerm A) → A)
  evalCl Mo (sing x1) = x1
  
  evalCl Mo eCl = (e Mo)
  
  evalCl Mo (opCl x1 x2) = ((op Mo) (evalCl Mo x1) (evalCl Mo x2))
  
  evalOpB : ({A : Set} (n : Nat) → (Monoid A) → (Vec A n) → (OpMonoidTerm n) → A)
  evalOpB n Mo vars (v x1) = (lookup vars x1)
  
  evalOpB n Mo vars eOL = (e Mo)
  
  evalOpB n Mo vars (opOL x1 x2) = ((op Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))
  
  evalOp : ({A : Set} (n : Nat) → (Monoid A) → (Vec A n) → (OpMonoidTerm2 n A) → A)
  evalOp n Mo vars (v2 x1) = (lookup vars x1)
  
  evalOp n Mo vars (sing2 x1) = x1
  
  evalOp n Mo vars eOL2 = (e Mo)
  
  evalOp n Mo vars (opOL2 x1 x2) = ((op Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))
  
  inductionB : ((P : MonoidTerm → Set) → (P eL) → ((x1 x2 : MonoidTerm) → (P x1) → (P x2) → (P (opL x1 x2))) → ((x : MonoidTerm) → (P x)))
  inductionB p pel popl eL = pel
  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))
  
  inductionCl : ((A : Set) (P : (ClMonoidTerm A) → Set) → ((x1 : A) → (P (sing x1))) → (P eCl) → ((x1 x2 : (ClMonoidTerm A)) → (P x1) → (P x2) → (P (opCl x1 x2))) → ((x : (ClMonoidTerm A)) → (P x)))
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)
  
  inductionCl _ p psing pecl popcl eCl = pecl
  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))
  
  inductionOpB : ((n : Nat) (P : (OpMonoidTerm n) → Set) → ((fin : (Fin n)) → (P (v fin))) → (P eOL) → ((x1 x2 : (OpMonoidTerm n)) → (P x1) → (P x2) → (P (opOL x1 x2))) → ((x : (OpMonoidTerm n)) → (P x)))
  inductionOpB _ p pv peol popol (v x1) = (pv x1)
  
  inductionOpB _ p pv peol popol eOL = peol
  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))
  
  inductionOp : ((n : Nat) (A : Set) (P : (OpMonoidTerm2 n A) → Set) → ((fin : (Fin n)) → (P (v2 fin))) → ((x1 : A) → (P (sing2 x1))) → (P eOL2) → ((x1 x2 : (OpMonoidTerm2 n A)) → (P x1) → (P x2) → (P (opOL2 x1 x2))) → ((x : (OpMonoidTerm2 n A)) → (P x)))
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))
  
  eL' : ( MonoidTerm)
  eL'  = eL
  
  opL' : ( MonoidTerm → MonoidTerm → MonoidTerm)
  opL' x1 x2 = (opL x1 x2)
  
  stageB : MonoidTerm → (Staged MonoidTerm)
  stageB eL = (Now eL)
  
  stageB (opL x1 x2) = (stage2 opL' (codeLift2 opL') (stageB x1) (stageB x2))
  
  eCl' : ({A : Set} → (ClMonoidTerm A))
  eCl'  = eCl
  
  opCl' : ({A : Set} → (ClMonoidTerm A) → (ClMonoidTerm A) → (ClMonoidTerm A))
  opCl' x1 x2 = (opCl x1 x2)
  
  stageCl : ((A : Set) → (ClMonoidTerm A) → (Staged (ClMonoidTerm A)))
  stageCl _ (sing x1) = (Now (sing x1))
  
  stageCl _ eCl = (Now eCl)
  
  stageCl _ (opCl x1 x2) = (stage2 opCl' (codeLift2 opCl') ((stageCl _) x1) ((stageCl _) x2))
  
  eOL' : ({n : Nat} → (OpMonoidTerm n))
  eOL'  = eOL
  
  opOL' : ({n : Nat} → (OpMonoidTerm n) → (OpMonoidTerm n) → (OpMonoidTerm n))
  opOL' x1 x2 = (opOL x1 x2)
  
  stageOpB : ((n : Nat) → (OpMonoidTerm n) → (Staged (OpMonoidTerm n)))
  stageOpB _ (v x1) = (const (code (v x1)))
  
  stageOpB _ eOL = (Now eOL)
  
  stageOpB _ (opOL x1 x2) = (stage2 opOL' (codeLift2 opOL') ((stageOpB _) x1) ((stageOpB _) x2))
  
  eOL2' : ({n : Nat} {A : Set} → (OpMonoidTerm2 n A))
  eOL2'  = eOL2
  
  opOL2' : ({n : Nat} {A : Set} → (OpMonoidTerm2 n A) → (OpMonoidTerm2 n A) → (OpMonoidTerm2 n A))
  opOL2' x1 x2 = (opOL2 x1 x2)
  
  stageOp : ((n : Nat) (A : Set) → (OpMonoidTerm2 n A) → (Staged (OpMonoidTerm2 n A)))
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))
  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))
  
  stageOp _ _ eOL2 = (Now eOL2)
  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2' (codeLift2 opOL2') ((stageOp _ _) x1) ((stageOp _ _) x2))
  
  record Tagless (A : Set) (Repr : Set → Set) : Set where
    constructor tagless
    field
      eT : (Repr A)
      opT : (Repr A) → (Repr A) → (Repr A) 
   
