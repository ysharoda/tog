
module BooleanGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BooleanGroup  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      unipotence : ( {x : A} → (op x x) ≡ e)  
  
  open BooleanGroup
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      unipotenceP : ( {xP : (Prod A A)} → (opP xP xP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Bo1 : (BooleanGroup A1)) (Bo2 : (BooleanGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Bo1)) ≡ (e Bo2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Bo1) x1 x2)) ≡ ((op Bo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bo1 : (BooleanGroup A1)) (Bo2 : (BooleanGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Bo1) (e Bo2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Bo1) x1 x2) ((op Bo2) y1 y2)))))  
  
  data BooleanGroupTerm   : Set where 
      eL : BooleanGroupTerm 
      opL : (BooleanGroupTerm → (BooleanGroupTerm → BooleanGroupTerm))  
      
  data ClBooleanGroupTerm  (A : Set) : Set where 
      sing : (A → (ClBooleanGroupTerm A)) 
      eCl : (ClBooleanGroupTerm A) 
      opCl : ((ClBooleanGroupTerm A) → ((ClBooleanGroupTerm A) → (ClBooleanGroupTerm A)))  
      
  data OpBooleanGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBooleanGroupTerm n)) 
      eOL : (OpBooleanGroupTerm n) 
      opOL : ((OpBooleanGroupTerm n) → ((OpBooleanGroupTerm n) → (OpBooleanGroupTerm n)))  
      
  data OpBooleanGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBooleanGroupTerm2 n A)) 
      sing2 : (A → (OpBooleanGroupTerm2 n A)) 
      eOL2 : (OpBooleanGroupTerm2 n A) 
      opOL2 : ((OpBooleanGroupTerm2 n A) → ((OpBooleanGroupTerm2 n A) → (OpBooleanGroupTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClBooleanGroupTerm A) → (ClBooleanGroupTerm A)) 
  simplifyCl _ (opCl eCl x) = x  
  simplifyCl _ (opCl x eCl) = x  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpBooleanGroupTerm n) → (OpBooleanGroupTerm n)) 
  simplifyOpB _ (opOL eOL x) = x  
  simplifyOpB _ (opOL x eOL) = x  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpBooleanGroupTerm2 n A) → (OpBooleanGroupTerm2 n A)) 
  simplifyOp _ _ (opOL2 eOL2 x) = x  
  simplifyOp _ _ (opOL2 x eOL2) = x  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BooleanGroup A) → (BooleanGroupTerm → A)) 
  evalB Bo eL = (e Bo)  
  evalB Bo (opL x1 x2) = ((op Bo) (evalB Bo x1) (evalB Bo x2))  
  evalCl :  {A : Set} →  ((BooleanGroup A) → ((ClBooleanGroupTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo eCl = (e Bo)  
  evalCl Bo (opCl x1 x2) = ((op Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((BooleanGroup A) → ((Vec A n) → ((OpBooleanGroupTerm n) → A))) 
  evalOpB n Bo vars (v x1) = (lookup vars x1)  
  evalOpB n Bo vars eOL = (e Bo)  
  evalOpB n Bo vars (opOL x1 x2) = ((op Bo) (evalOpB n Bo vars x1) (evalOpB n Bo vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((BooleanGroup A) → ((Vec A n) → ((OpBooleanGroupTerm2 n A) → A))) 
  evalOp n Bo vars (v2 x1) = (lookup vars x1)  
  evalOp n Bo vars (sing2 x1) = x1  
  evalOp n Bo vars eOL2 = (e Bo)  
  evalOp n Bo vars (opOL2 x1 x2) = ((op Bo) (evalOp n Bo vars x1) (evalOp n Bo vars x2))  
  inductionB :  (P : (BooleanGroupTerm → Set)) →  ((P eL) → (( (x1 x2 : BooleanGroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : BooleanGroupTerm) → (P x)))) 
  inductionB p pel popl eL = pel  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))  
  inductionCl :  (A : Set) (P : ((ClBooleanGroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClBooleanGroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClBooleanGroupTerm A)) → (P x))))) 
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pecl popcl eCl = pecl  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpBooleanGroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpBooleanGroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpBooleanGroupTerm n)) → (P x))))) 
  inductionOpB _ p pv peol popol (v x1) = (pv x1)  
  inductionOpB _ p pv peol popol eOL = peol  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpBooleanGroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpBooleanGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpBooleanGroupTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))  
  stageB :  (BooleanGroupTerm → (Staged BooleanGroupTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClBooleanGroupTerm A) → (Staged (ClBooleanGroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpBooleanGroupTerm n) → (Staged (OpBooleanGroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpBooleanGroupTerm2 n A) → (Staged (OpBooleanGroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 