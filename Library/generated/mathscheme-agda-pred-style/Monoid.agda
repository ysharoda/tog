
module Monoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMonoid  (A : Set) (op : (A → (A → A))) (e : A) : Set where 
     field  
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z)))  
  
  record Monoid  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      isMonoid : (IsMonoid A op e)  
  
  open Monoid
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (Monoid A1)) (Mo2 : (Monoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Mo1) x1 x2)) ≡ ((op Mo2) (hom x1) (hom x2))) 
      pres-e : (hom (e Mo1)) ≡ (e Mo2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (Monoid A1)) (Mo2 : (Monoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2))))) 
      interp-e : (interp (e Mo1) (e Mo2))  
  
  data MonoidTerm   : Set where 
      opL : (MonoidTerm → (MonoidTerm → MonoidTerm)) 
      eL : MonoidTerm  
      
  data ClMonoidTerm  (A : Set) : Set where 
      sing : (A → (ClMonoidTerm A)) 
      opCl : ((ClMonoidTerm A) → ((ClMonoidTerm A) → (ClMonoidTerm A))) 
      eCl : (ClMonoidTerm A)  
      
  data OpMonoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMonoidTerm n)) 
      opOL : ((OpMonoidTerm n) → ((OpMonoidTerm n) → (OpMonoidTerm n))) 
      eOL : (OpMonoidTerm n)  
      
  data OpMonoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMonoidTerm2 n A)) 
      sing2 : (A → (OpMonoidTerm2 n A)) 
      opOL2 : ((OpMonoidTerm2 n A) → ((OpMonoidTerm2 n A) → (OpMonoidTerm2 n A))) 
      eOL2 : (OpMonoidTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClMonoidTerm A) → (ClMonoidTerm A)) 
  simplifyCl (opCl eCl x) = x  
  simplifyCl (opCl x eCl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpMonoidTerm n) → (OpMonoidTerm n)) 
  simplifyOpB (opOL eOL x) = x  
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpMonoidTerm2 n A) → (OpMonoidTerm2 n A)) 
  simplifyOp (opOL2 eOL2 x) = x  
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Monoid A) → (MonoidTerm → A)) 
  evalB Mo (opL x1 x2) = ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo eL = (e Mo)  
  evalCl :  {A : Set} →  ((Monoid A) → ((ClMonoidTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (opCl x1 x2) = ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo eCl = (e Mo)  
  evalOpB :  {A : Set} {n : Nat} →  ((Monoid A) → ((Vec A n) → ((OpMonoidTerm n) → A))) 
  evalOpB Mo vars (v x1) = (lookup vars x1)  
  evalOpB Mo vars (opOL x1 x2) = ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  evalOpB Mo vars eOL = (e Mo)  
  evalOp :  {A : Set} {n : Nat} →  ((Monoid A) → ((Vec A n) → ((OpMonoidTerm2 n A) → A))) 
  evalOp Mo vars (v2 x1) = (lookup vars x1)  
  evalOp Mo vars (sing2 x1) = x1  
  evalOp Mo vars (opOL2 x1 x2) = ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  evalOp Mo vars eOL2 = (e Mo)  
  inductionB :  {P : (MonoidTerm → Set)} →  (( (x1 x2 : MonoidTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : MonoidTerm) → (P x)))) 
  inductionB popl pel (opL x1 x2) = (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  inductionB popl pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClMonoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMonoidTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClMonoidTerm A)) → (P x))))) 
  inductionCl psing popcl pecl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  inductionCl psing popcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpMonoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMonoidTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpMonoidTerm n)) → (P x))))) 
  inductionOpB pv popol peol (v x1) = (pv x1)  
  inductionOpB pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  inductionOpB pv popol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpMonoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpMonoidTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (MonoidTerm → (Staged MonoidTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClMonoidTerm A) → (Staged (ClMonoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpMonoidTerm n) → (Staged (OpMonoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpMonoidTerm2 n A) → (Staged (OpMonoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 