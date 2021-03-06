
module AntiAbsorbent   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAntiAbsorbent  (A : Set) (op : (A → (A → A))) : Set where 
     field  
      antiAbsorbent : ( {x y : A} → (op x (op x y)) ≡ y)  
  
  record AntiAbsorbent  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      isAntiAbsorbent : (IsAntiAbsorbent A op)  
  
  open AntiAbsorbent
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      antiAbsorbentP : ( {xP yP : (Prod A A)} → (opP xP (opP xP yP)) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (An1 : (AntiAbsorbent A1)) (An2 : (AntiAbsorbent A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op An1) x1 x2)) ≡ ((op An2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (An1 : (AntiAbsorbent A1)) (An2 : (AntiAbsorbent A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op An1) x1 x2) ((op An2) y1 y2)))))  
  
  data AntiAbsorbentTerm   : Set where 
      opL : (AntiAbsorbentTerm → (AntiAbsorbentTerm → AntiAbsorbentTerm))  
      
  data ClAntiAbsorbentTerm  (A : Set) : Set where 
      sing : (A → (ClAntiAbsorbentTerm A)) 
      opCl : ((ClAntiAbsorbentTerm A) → ((ClAntiAbsorbentTerm A) → (ClAntiAbsorbentTerm A)))  
      
  data OpAntiAbsorbentTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAntiAbsorbentTerm n)) 
      opOL : ((OpAntiAbsorbentTerm n) → ((OpAntiAbsorbentTerm n) → (OpAntiAbsorbentTerm n)))  
      
  data OpAntiAbsorbentTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAntiAbsorbentTerm2 n A)) 
      sing2 : (A → (OpAntiAbsorbentTerm2 n A)) 
      opOL2 : ((OpAntiAbsorbentTerm2 n A) → ((OpAntiAbsorbentTerm2 n A) → (OpAntiAbsorbentTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClAntiAbsorbentTerm A) → (ClAntiAbsorbentTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAntiAbsorbentTerm n) → (OpAntiAbsorbentTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAntiAbsorbentTerm2 n A) → (OpAntiAbsorbentTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AntiAbsorbent A) → (AntiAbsorbentTerm → A)) 
  evalB An (opL x1 x2) = ((op An) (evalB An x1) (evalB An x2))  
  evalCl :  {A : Set} →  ((AntiAbsorbent A) → ((ClAntiAbsorbentTerm A) → A)) 
  evalCl An (sing x1) = x1  
  evalCl An (opCl x1 x2) = ((op An) (evalCl An x1) (evalCl An x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((AntiAbsorbent A) → ((Vec A n) → ((OpAntiAbsorbentTerm n) → A))) 
  evalOpB An vars (v x1) = (lookup vars x1)  
  evalOpB An vars (opOL x1 x2) = ((op An) (evalOpB An vars x1) (evalOpB An vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((AntiAbsorbent A) → ((Vec A n) → ((OpAntiAbsorbentTerm2 n A) → A))) 
  evalOp An vars (v2 x1) = (lookup vars x1)  
  evalOp An vars (sing2 x1) = x1  
  evalOp An vars (opOL2 x1 x2) = ((op An) (evalOp An vars x1) (evalOp An vars x2))  
  inductionB :  {P : (AntiAbsorbentTerm → Set)} →  (( (x1 x2 : AntiAbsorbentTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : AntiAbsorbentTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClAntiAbsorbentTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAntiAbsorbentTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClAntiAbsorbentTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpAntiAbsorbentTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAntiAbsorbentTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpAntiAbsorbentTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAntiAbsorbentTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAntiAbsorbentTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpAntiAbsorbentTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (AntiAbsorbentTerm → (Staged AntiAbsorbentTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClAntiAbsorbentTerm A) → (Staged (ClAntiAbsorbentTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpAntiAbsorbentTerm n) → (Staged (OpAntiAbsorbentTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpAntiAbsorbentTerm2 n A) → (Staged (OpAntiAbsorbentTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 