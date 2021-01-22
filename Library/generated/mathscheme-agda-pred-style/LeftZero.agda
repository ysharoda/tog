
module LeftZero   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftZero  (A : Set) (e : A) (op : (A → (A → A))) : Set where 
     field  
      leftZero_op_e : ( {x : A} → (op e x) ≡ e)  
  
  record LeftZero  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      isLeftZero : (IsLeftZero A e op)  
  
  open LeftZero
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftZero_op_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftZero A1)) (Le2 : (LeftZero A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Le1)) ≡ (e Le2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftZero A1)) (Le2 : (LeftZero A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Le1) (e Le2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))  
  
  data LeftZeroTerm   : Set where 
      eL : LeftZeroTerm 
      opL : (LeftZeroTerm → (LeftZeroTerm → LeftZeroTerm))  
      
  data ClLeftZeroTerm  (A : Set) : Set where 
      sing : (A → (ClLeftZeroTerm A)) 
      eCl : (ClLeftZeroTerm A) 
      opCl : ((ClLeftZeroTerm A) → ((ClLeftZeroTerm A) → (ClLeftZeroTerm A)))  
      
  data OpLeftZeroTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftZeroTerm n)) 
      eOL : (OpLeftZeroTerm n) 
      opOL : ((OpLeftZeroTerm n) → ((OpLeftZeroTerm n) → (OpLeftZeroTerm n)))  
      
  data OpLeftZeroTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftZeroTerm2 n A)) 
      sing2 : (A → (OpLeftZeroTerm2 n A)) 
      eOL2 : (OpLeftZeroTerm2 n A) 
      opOL2 : ((OpLeftZeroTerm2 n A) → ((OpLeftZeroTerm2 n A) → (OpLeftZeroTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLeftZeroTerm A) → (ClLeftZeroTerm A)) 
  simplifyCl eCl = eCl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLeftZeroTerm n) → (OpLeftZeroTerm n)) 
  simplifyOpB eOL = eOL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLeftZeroTerm2 n A) → (OpLeftZeroTerm2 n A)) 
  simplifyOp eOL2 = eOL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftZero A) → (LeftZeroTerm → A)) 
  evalB Le eL = (e Le)  
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftZero A) → ((ClLeftZeroTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le eCl = (e Le)  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((LeftZero A) → ((Vec A n) → ((OpLeftZeroTerm n) → A))) 
  evalOpB Le vars (v x1) = (lookup vars x1)  
  evalOpB Le vars eOL = (e Le)  
  evalOpB Le vars (opOL x1 x2) = ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((LeftZero A) → ((Vec A n) → ((OpLeftZeroTerm2 n A) → A))) 
  evalOp Le vars (v2 x1) = (lookup vars x1)  
  evalOp Le vars (sing2 x1) = x1  
  evalOp Le vars eOL2 = (e Le)  
  evalOp Le vars (opOL2 x1 x2) = ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  inductionB :  {P : (LeftZeroTerm → Set)} →  ((P eL) → (( (x1 x2 : LeftZeroTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : LeftZeroTerm) → (P x)))) 
  inductionB pel popl eL = pel  
  inductionB pel popl (opL x1 x2) = (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  inductionCl :  {A : Set} {P : ((ClLeftZeroTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClLeftZeroTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClLeftZeroTerm A)) → (P x))))) 
  inductionCl psing pecl popcl (sing x1) = (psing x1)  
  inductionCl psing pecl popcl eCl = pecl  
  inductionCl psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLeftZeroTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpLeftZeroTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpLeftZeroTerm n)) → (P x))))) 
  inductionOpB pv peol popol (v x1) = (pv x1)  
  inductionOpB pv peol popol eOL = peol  
  inductionOpB pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLeftZeroTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpLeftZeroTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpLeftZeroTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  stageB :  (LeftZeroTerm → (Staged LeftZeroTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLeftZeroTerm A) → (Staged (ClLeftZeroTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl eCl = (Now eCl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLeftZeroTerm n) → (Staged (OpLeftZeroTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB eOL = (Now eOL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLeftZeroTerm2 n A) → (Staged (OpLeftZeroTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 