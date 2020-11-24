
 module RightUnital  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightUnital (A : Set) : Set where
    constructor RightUnitalC
    field
      e : A
      op : A → A → A
      runit_e : ({x : A} → (op x e) ≡ x) 
  
  open RightUnital
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
      runit_eP : ({xP : (Prod A A)} → (opP xP eP) ≡ xP) 
  
  record Hom {A1 : Set} {A2 : Set} (Ri1 : (RightUnital A1)) (Ri2 : (RightUnital A2)) : Set where
    constructor HomC
    field
      hom : A1 → A2
      pres-e : (hom (e Ri1)) ≡ (e Ri2)
      pres-op : ({x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2))) 
  
  record RelInterp {A1 : Set} {A2 : Set} (Ri1 : (RightUnital A1)) (Ri2 : (RightUnital A2)) : Set₁ where
    constructor RelInterpC
    field
      interp : A1 → A2 → Set
      interp-e : (interp (e Ri1) (e Ri2))
      interp-op : ({x1 x2 : A1} {y1 y2 : A2} → (interp x1 y1) → (interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2))) 
  
  data RightUnitalTerm  : Set where
    eL : RightUnitalTerm
    opL : RightUnitalTerm → RightUnitalTerm → RightUnitalTerm 
  
  data ClRightUnitalTerm (A : Set) : Set where
    sing : A → (ClRightUnitalTerm A)
    eCl : (ClRightUnitalTerm A)
    opCl : (ClRightUnitalTerm A) → (ClRightUnitalTerm A) → (ClRightUnitalTerm A) 
  
  data OpRightUnitalTerm (n : Nat) : Set where
    v : (Fin n) → (OpRightUnitalTerm n)
    eOL : (OpRightUnitalTerm n)
    opOL : (OpRightUnitalTerm n) → (OpRightUnitalTerm n) → (OpRightUnitalTerm n) 
  
  data OpRightUnitalTerm2 (n : Nat) (A : Set) : Set where
    v2 : (Fin n) → (OpRightUnitalTerm2 n A)
    sing2 : A → (OpRightUnitalTerm2 n A)
    eOL2 : (OpRightUnitalTerm2 n A)
    opOL2 : (OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A) 
  
  simplifyB : RightUnitalTerm → RightUnitalTerm
  simplifyB (opL x eL) = x
  
  simplifyB eL = eL
  
  simplifyB (opL x1 x2) = (opL (simplifyB x1) (simplifyB x2))
  
  simplifyCl : ((A : Set) → (ClRightUnitalTerm A) → (ClRightUnitalTerm A))
  simplifyCl _ (opCl x eCl) = x
  
  simplifyCl _ eCl = eCl
  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))
  
  simplifyCl _ (sing x1) = (sing x1)
  
  simplifyOpB : ((n : Nat) → (OpRightUnitalTerm n) → (OpRightUnitalTerm n))
  simplifyOpB _ (opOL x eOL) = x
  
  simplifyOpB _ eOL = eOL
  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))
  
  simplifyOpB _ (v x1) = (v x1)
  
  simplifyOp : ((n : Nat) (A : Set) → (OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A))
  simplifyOp _ _ (opOL2 x eOL2) = x
  
  simplifyOp _ _ eOL2 = eOL2
  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))
  
  simplifyOp _ _ (v2 x1) = (v2 x1)
  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)
  
  evalB : ({A : Set} → (RightUnital A) → RightUnitalTerm → A)
  evalB Ri eL = (e Ri)
  
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))
  
  evalCl : ({A : Set} → (RightUnital A) → (ClRightUnitalTerm A) → A)
  evalCl Ri (sing x1) = x1
  
  evalCl Ri eCl = (e Ri)
  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))
  
  evalOpB : ({A : Set} (n : Nat) → (RightUnital A) → (Vec A n) → (OpRightUnitalTerm n) → A)
  evalOpB n Ri vars (v x1) = (lookup vars x1)
  
  evalOpB n Ri vars eOL = (e Ri)
  
  evalOpB n Ri vars (opOL x1 x2) = ((op Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))
  
  evalOp : ({A : Set} (n : Nat) → (RightUnital A) → (Vec A n) → (OpRightUnitalTerm2 n A) → A)
  evalOp n Ri vars (v2 x1) = (lookup vars x1)
  
  evalOp n Ri vars (sing2 x1) = x1
  
  evalOp n Ri vars eOL2 = (e Ri)
  
  evalOp n Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))
  
  inductionB : ((P : RightUnitalTerm → Set) → (P eL) → ((x1 x2 : RightUnitalTerm) → (P x1) → (P x2) → (P (opL x1 x2))) → ((x : RightUnitalTerm) → (P x)))
  inductionB p pel popl eL = pel
  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))
  
  inductionCl : ((A : Set) (P : (ClRightUnitalTerm A) → Set) → ((x1 : A) → (P (sing x1))) → (P eCl) → ((x1 x2 : (ClRightUnitalTerm A)) → (P x1) → (P x2) → (P (opCl x1 x2))) → ((x : (ClRightUnitalTerm A)) → (P x)))
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)
  
  inductionCl _ p psing pecl popcl eCl = pecl
  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))
  
  inductionOpB : ((n : Nat) (P : (OpRightUnitalTerm n) → Set) → ((fin : (Fin n)) → (P (v fin))) → (P eOL) → ((x1 x2 : (OpRightUnitalTerm n)) → (P x1) → (P x2) → (P (opOL x1 x2))) → ((x : (OpRightUnitalTerm n)) → (P x)))
  inductionOpB _ p pv peol popol (v x1) = (pv x1)
  
  inductionOpB _ p pv peol popol eOL = peol
  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))
  
  inductionOp : ((n : Nat) (A : Set) (P : (OpRightUnitalTerm2 n A) → Set) → ((fin : (Fin n)) → (P (v2 fin))) → ((x1 : A) → (P (sing2 x1))) → (P eOL2) → ((x1 x2 : (OpRightUnitalTerm2 n A)) → (P x1) → (P x2) → (P (opOL2 x1 x2))) → ((x : (OpRightUnitalTerm2 n A)) → (P x)))
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2
  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))
  
  eL' : ( RightUnitalTerm)
  eL'  = eL
  
  opL' : ( RightUnitalTerm → RightUnitalTerm → RightUnitalTerm)
  opL' x1 x2 = (opL x1 x2)
  
  stageB : RightUnitalTerm → (Staged RightUnitalTerm)
  stageB eL = (Now eL)
  
  stageB (opL x1 x2) = (stage2 opL' (codeLift2 opL') (stageB x1) (stageB x2))
  
  eCl' : ({A : Set} → (ClRightUnitalTerm A))
  eCl'  = eCl
  
  opCl' : ({A : Set} → (ClRightUnitalTerm A) → (ClRightUnitalTerm A) → (ClRightUnitalTerm A))
  opCl' x1 x2 = (opCl x1 x2)
  
  stageCl : ((A : Set) → (ClRightUnitalTerm A) → (Staged (ClRightUnitalTerm A)))
  stageCl _ (sing x1) = (Now (sing x1))
  
  stageCl _ eCl = (Now eCl)
  
  stageCl _ (opCl x1 x2) = (stage2 opCl' (codeLift2 opCl') ((stageCl _) x1) ((stageCl _) x2))
  
  eOL' : ({n : Nat} → (OpRightUnitalTerm n))
  eOL'  = eOL
  
  opOL' : ({n : Nat} → (OpRightUnitalTerm n) → (OpRightUnitalTerm n) → (OpRightUnitalTerm n))
  opOL' x1 x2 = (opOL x1 x2)
  
  stageOpB : ((n : Nat) → (OpRightUnitalTerm n) → (Staged (OpRightUnitalTerm n)))
  stageOpB _ (v x1) = (const (code (v x1)))
  
  stageOpB _ eOL = (Now eOL)
  
  stageOpB _ (opOL x1 x2) = (stage2 opOL' (codeLift2 opOL') ((stageOpB _) x1) ((stageOpB _) x2))
  
  eOL2' : ({n : Nat} {A : Set} → (OpRightUnitalTerm2 n A))
  eOL2'  = eOL2
  
  opOL2' : ({n : Nat} {A : Set} → (OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A) → (OpRightUnitalTerm2 n A))
  opOL2' x1 x2 = (opOL2 x1 x2)
  
  stageOp : ((n : Nat) (A : Set) → (OpRightUnitalTerm2 n A) → (Staged (OpRightUnitalTerm2 n A)))
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))
  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))
  
  stageOp _ _ eOL2 = (Now eOL2)
  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2' (codeLift2 opOL2') ((stageOp _ _) x1) ((stageOp _ _) x2))
  
  record Tagless (A : Set) (Repr : Set → Set) : Set where
    constructor tagless
    field
      eT : (Repr A)
      opT : (Repr A) → (Repr A) → (Repr A) 
   
