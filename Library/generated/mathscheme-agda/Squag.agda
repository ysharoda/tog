
module Squag   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Squag  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x)) 
      antiAbsorbent : ( {x y : A} → (op x (op x y)) ≡ y) 
      idempotent_op : ( {x : A} → (op x x) ≡ x)  
  
  open Squag
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP)) 
      antiAbsorbentP : ( {xP yP : (Prod A A)} → (opP xP (opP xP yP)) ≡ yP) 
      idempotent_opP : ( {xP : (Prod A A)} → (opP xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Sq1 : (Squag A1)) (Sq2 : (Squag A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Sq1) x1 x2)) ≡ ((op Sq2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Sq1 : (Squag A1)) (Sq2 : (Squag A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Sq1) x1 x2) ((op Sq2) y1 y2)))))  
  
  data SquagTerm   : Set where 
      opL : (SquagTerm → (SquagTerm → SquagTerm))  
      
  data ClSquagTerm  (A : Set) : Set where 
      sing : (A → (ClSquagTerm A)) 
      opCl : ((ClSquagTerm A) → ((ClSquagTerm A) → (ClSquagTerm A)))  
      
  data OpSquagTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpSquagTerm n)) 
      opOL : ((OpSquagTerm n) → ((OpSquagTerm n) → (OpSquagTerm n)))  
      
  data OpSquagTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpSquagTerm2 n A)) 
      sing2 : (A → (OpSquagTerm2 n A)) 
      opOL2 : ((OpSquagTerm2 n A) → ((OpSquagTerm2 n A) → (OpSquagTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClSquagTerm A) → (ClSquagTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpSquagTerm n) → (OpSquagTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpSquagTerm2 n A) → (OpSquagTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Squag A) → (SquagTerm → A)) 
  evalB Sq (opL x1 x2) = ((op Sq) (evalB Sq x1) (evalB Sq x2))  
  evalCl :  {A : Set} →  ((Squag A) → ((ClSquagTerm A) → A)) 
  evalCl Sq (sing x1) = x1  
  evalCl Sq (opCl x1 x2) = ((op Sq) (evalCl Sq x1) (evalCl Sq x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Squag A) → ((Vec A n) → ((OpSquagTerm n) → A))) 
  evalOpB n Sq vars (v x1) = (lookup vars x1)  
  evalOpB n Sq vars (opOL x1 x2) = ((op Sq) (evalOpB n Sq vars x1) (evalOpB n Sq vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Squag A) → ((Vec A n) → ((OpSquagTerm2 n A) → A))) 
  evalOp n Sq vars (v2 x1) = (lookup vars x1)  
  evalOp n Sq vars (sing2 x1) = x1  
  evalOp n Sq vars (opOL2 x1 x2) = ((op Sq) (evalOp n Sq vars x1) (evalOp n Sq vars x2))  
  inductionB :  (P : (SquagTerm → Set)) →  (( (x1 x2 : SquagTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : SquagTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClSquagTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClSquagTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClSquagTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpSquagTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpSquagTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpSquagTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpSquagTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpSquagTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpSquagTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (SquagTerm → (Staged SquagTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClSquagTerm A) → (Staged (ClSquagTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpSquagTerm n) → (Staged (OpSquagTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpSquagTerm2 n A) → (Staged (OpSquagTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 