
module LeftCancellativeMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftCancellativeMagma  (A : Set) (op : (A → (A → A))) : Set where 
     field  
      leftCancellative : ( {x y z : A} → ((op z x) ≡ (op z y) → x ≡ y))  
  
  record LeftCancellativeMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      isLeftCancellativeMagma : (IsLeftCancellativeMagma A op)  
  
  open LeftCancellativeMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP zP xP) ≡ (opP zP yP) → xP ≡ yP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftCancellativeMagma A1)) (Le2 : (LeftCancellativeMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftCancellativeMagma A1)) (Le2 : (LeftCancellativeMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))  
  
  data LeftCancellativeMagmaTerm   : Set where 
      opL : (LeftCancellativeMagmaTerm → (LeftCancellativeMagmaTerm → LeftCancellativeMagmaTerm))  
      
  data ClLeftCancellativeMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClLeftCancellativeMagmaTerm A)) 
      opCl : ((ClLeftCancellativeMagmaTerm A) → ((ClLeftCancellativeMagmaTerm A) → (ClLeftCancellativeMagmaTerm A)))  
      
  data OpLeftCancellativeMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftCancellativeMagmaTerm n)) 
      opOL : ((OpLeftCancellativeMagmaTerm n) → ((OpLeftCancellativeMagmaTerm n) → (OpLeftCancellativeMagmaTerm n)))  
      
  data OpLeftCancellativeMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftCancellativeMagmaTerm2 n A)) 
      sing2 : (A → (OpLeftCancellativeMagmaTerm2 n A)) 
      opOL2 : ((OpLeftCancellativeMagmaTerm2 n A) → ((OpLeftCancellativeMagmaTerm2 n A) → (OpLeftCancellativeMagmaTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLeftCancellativeMagmaTerm A) → (ClLeftCancellativeMagmaTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLeftCancellativeMagmaTerm n) → (OpLeftCancellativeMagmaTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLeftCancellativeMagmaTerm2 n A) → (OpLeftCancellativeMagmaTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftCancellativeMagma A) → (LeftCancellativeMagmaTerm → A)) 
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftCancellativeMagma A) → ((ClLeftCancellativeMagmaTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((LeftCancellativeMagma A) → ((Vec A n) → ((OpLeftCancellativeMagmaTerm n) → A))) 
  evalOpB Le vars (v x1) = (lookup vars x1)  
  evalOpB Le vars (opOL x1 x2) = ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((LeftCancellativeMagma A) → ((Vec A n) → ((OpLeftCancellativeMagmaTerm2 n A) → A))) 
  evalOp Le vars (v2 x1) = (lookup vars x1)  
  evalOp Le vars (sing2 x1) = x1  
  evalOp Le vars (opOL2 x1 x2) = ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  inductionB :  {P : (LeftCancellativeMagmaTerm → Set)} →  (( (x1 x2 : LeftCancellativeMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : LeftCancellativeMagmaTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClLeftCancellativeMagmaTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftCancellativeMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClLeftCancellativeMagmaTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLeftCancellativeMagmaTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftCancellativeMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpLeftCancellativeMagmaTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLeftCancellativeMagmaTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftCancellativeMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpLeftCancellativeMagmaTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (LeftCancellativeMagmaTerm → (Staged LeftCancellativeMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLeftCancellativeMagmaTerm A) → (Staged (ClLeftCancellativeMagmaTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLeftCancellativeMagmaTerm n) → (Staged (OpLeftCancellativeMagmaTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLeftCancellativeMagmaTerm2 n A) → (Staged (OpLeftCancellativeMagmaTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 