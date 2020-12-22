
module Sloop   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsSloop  (A : Set) (e : A) (op : (A → (A → A))) : Set where 
     field  
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x)) 
      antiAbsorbent : ( {x y : A} → (op x (op x y)) ≡ y) 
      unipotence : ( {x : A} → (op x x) ≡ e)  
  
  record Sloop  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      isSloop : (IsSloop A e op)  
  
  open Sloop
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP)) 
      antiAbsorbentP : ( {xP yP : (Prod A A)} → (opP xP (opP xP yP)) ≡ yP) 
      unipotenceP : ( {xP : (Prod A A)} → (opP xP xP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Sl1 : (Sloop A1)) (Sl2 : (Sloop A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Sl1)) ≡ (e Sl2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Sl1) x1 x2)) ≡ ((op Sl2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Sl1 : (Sloop A1)) (Sl2 : (Sloop A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Sl1) (e Sl2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Sl1) x1 x2) ((op Sl2) y1 y2)))))  
  
  data SloopLTerm   : Set where 
      eL : SloopLTerm 
      opL : (SloopLTerm → (SloopLTerm → SloopLTerm))  
      
  data ClSloopClTerm  (A : Set) : Set where 
      sing : (A → (ClSloopClTerm A)) 
      eCl : (ClSloopClTerm A) 
      opCl : ((ClSloopClTerm A) → ((ClSloopClTerm A) → (ClSloopClTerm A)))  
      
  data OpSloopOLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpSloopOLTerm n)) 
      eOL : (OpSloopOLTerm n) 
      opOL : ((OpSloopOLTerm n) → ((OpSloopOLTerm n) → (OpSloopOLTerm n)))  
      
  data OpSloopOL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpSloopOL2Term2 n A)) 
      sing2 : (A → (OpSloopOL2Term2 n A)) 
      eOL2 : (OpSloopOL2Term2 n A) 
      opOL2 : ((OpSloopOL2Term2 n A) → ((OpSloopOL2Term2 n A) → (OpSloopOL2Term2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClSloopClTerm A) → (ClSloopClTerm A)) 
  simplifyCl _ eCl = eCl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpSloopOLTerm n) → (OpSloopOLTerm n)) 
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpSloopOL2Term2 n A) → (OpSloopOL2Term2 n A)) 
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Sloop A) → (SloopLTerm → A)) 
  evalB Sl eL = (e Sl)  
  evalB Sl (opL x1 x2) = ((op Sl) (evalB Sl x1) (evalB Sl x2))  
  evalCl :  {A : Set} →  ((Sloop A) → ((ClSloopClTerm A) → A)) 
  evalCl Sl (sing x1) = x1  
  evalCl Sl eCl = (e Sl)  
  evalCl Sl (opCl x1 x2) = ((op Sl) (evalCl Sl x1) (evalCl Sl x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Sloop A) → ((Vec A n) → ((OpSloopOLTerm n) → A))) 
  evalOpB n Sl vars (v x1) = (lookup vars x1)  
  evalOpB n Sl vars eOL = (e Sl)  
  evalOpB n Sl vars (opOL x1 x2) = ((op Sl) (evalOpB n Sl vars x1) (evalOpB n Sl vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Sloop A) → ((Vec A n) → ((OpSloopOL2Term2 n A) → A))) 
  evalOp n Sl vars (v2 x1) = (lookup vars x1)  
  evalOp n Sl vars (sing2 x1) = x1  
  evalOp n Sl vars eOL2 = (e Sl)  
  evalOp n Sl vars (opOL2 x1 x2) = ((op Sl) (evalOp n Sl vars x1) (evalOp n Sl vars x2))  
  inductionB :  (P : (SloopLTerm → Set)) →  ((P eL) → (( (x1 x2 : SloopLTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : SloopLTerm) → (P x)))) 
  inductionB p pel popl eL = pel  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))  
  inductionCl :  (A : Set) (P : ((ClSloopClTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClSloopClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClSloopClTerm A)) → (P x))))) 
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pecl popcl eCl = pecl  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpSloopOLTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpSloopOLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpSloopOLTerm n)) → (P x))))) 
  inductionOpB _ p pv peol popol (v x1) = (pv x1)  
  inductionOpB _ p pv peol popol eOL = peol  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpSloopOL2Term2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpSloopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpSloopOL2Term2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))  
  stageB :  (SloopLTerm → (Staged SloopLTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClSloopClTerm A) → (Staged (ClSloopClTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpSloopOLTerm n) → (Staged (OpSloopOLTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpSloopOL2Term2 n A) → (Staged (OpSloopOL2Term2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 