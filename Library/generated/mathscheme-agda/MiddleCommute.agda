
module MiddleCommute   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MiddleCommute  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      middleCommute_* : ( {x y z : A} → (op (op (op x y) z) x) ≡ (op (op (op x z) y) x))  
  
  open MiddleCommute
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      middleCommute_*P : ( {xP yP zP : (Prod A A)} → (opP (opP (opP xP yP) zP) xP) ≡ (opP (opP (opP xP zP) yP) xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mi1 : (MiddleCommute A1)) (Mi2 : (MiddleCommute A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Mi1) x1 x2)) ≡ ((op Mi2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mi1 : (MiddleCommute A1)) (Mi2 : (MiddleCommute A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mi1) x1 x2) ((op Mi2) y1 y2)))))  
  
  data MiddleCommuteTerm   : Set where 
      opL : (MiddleCommuteTerm → (MiddleCommuteTerm → MiddleCommuteTerm))  
      
  data ClMiddleCommuteTerm  (A : Set) : Set where 
      sing : (A → (ClMiddleCommuteTerm A)) 
      opCl : ((ClMiddleCommuteTerm A) → ((ClMiddleCommuteTerm A) → (ClMiddleCommuteTerm A)))  
      
  data OpMiddleCommuteTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMiddleCommuteTerm n)) 
      opOL : ((OpMiddleCommuteTerm n) → ((OpMiddleCommuteTerm n) → (OpMiddleCommuteTerm n)))  
      
  data OpMiddleCommuteTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMiddleCommuteTerm2 n A)) 
      sing2 : (A → (OpMiddleCommuteTerm2 n A)) 
      opOL2 : ((OpMiddleCommuteTerm2 n A) → ((OpMiddleCommuteTerm2 n A) → (OpMiddleCommuteTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMiddleCommuteTerm A) → (ClMiddleCommuteTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMiddleCommuteTerm n) → (OpMiddleCommuteTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMiddleCommuteTerm2 n A) → (OpMiddleCommuteTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MiddleCommute A) → (MiddleCommuteTerm → A)) 
  evalB Mi (opL x1 x2) = ((op Mi) (evalB Mi x1) (evalB Mi x2))  
  evalCl :  {A : Set} →  ((MiddleCommute A) → ((ClMiddleCommuteTerm A) → A)) 
  evalCl Mi (sing x1) = x1  
  evalCl Mi (opCl x1 x2) = ((op Mi) (evalCl Mi x1) (evalCl Mi x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MiddleCommute A) → ((Vec A n) → ((OpMiddleCommuteTerm n) → A))) 
  evalOpB n Mi vars (v x1) = (lookup vars x1)  
  evalOpB n Mi vars (opOL x1 x2) = ((op Mi) (evalOpB n Mi vars x1) (evalOpB n Mi vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MiddleCommute A) → ((Vec A n) → ((OpMiddleCommuteTerm2 n A) → A))) 
  evalOp n Mi vars (v2 x1) = (lookup vars x1)  
  evalOp n Mi vars (sing2 x1) = x1  
  evalOp n Mi vars (opOL2 x1 x2) = ((op Mi) (evalOp n Mi vars x1) (evalOp n Mi vars x2))  
  inductionB :  (P : (MiddleCommuteTerm → Set)) →  (( (x1 x2 : MiddleCommuteTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : MiddleCommuteTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClMiddleCommuteTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMiddleCommuteTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClMiddleCommuteTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMiddleCommuteTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMiddleCommuteTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpMiddleCommuteTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMiddleCommuteTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMiddleCommuteTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpMiddleCommuteTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (MiddleCommuteTerm → (Staged MiddleCommuteTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMiddleCommuteTerm A) → (Staged (ClMiddleCommuteTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMiddleCommuteTerm n) → (Staged (OpMiddleCommuteTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMiddleCommuteTerm2 n A) → (Staged (OpMiddleCommuteTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 