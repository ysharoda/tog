
module LeftCancellativeSemigroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftCancellativeSemigroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      leftCancellative : ( {x y z : A} → ((op z x) ≡ (op z y) → x ≡ y))  
  
  open LeftCancellativeSemigroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      leftCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP zP xP) ≡ (opP zP yP) → xP ≡ yP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftCancellativeSemigroup A1)) (Le2 : (LeftCancellativeSemigroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftCancellativeSemigroup A1)) (Le2 : (LeftCancellativeSemigroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))  
  
  data LeftCancellativeSemigroupTerm   : Set where 
      opL : (LeftCancellativeSemigroupTerm → (LeftCancellativeSemigroupTerm → LeftCancellativeSemigroupTerm))  
      
  data ClLeftCancellativeSemigroupTerm  (A : Set) : Set where 
      sing : (A → (ClLeftCancellativeSemigroupTerm A)) 
      opCl : ((ClLeftCancellativeSemigroupTerm A) → ((ClLeftCancellativeSemigroupTerm A) → (ClLeftCancellativeSemigroupTerm A)))  
      
  data OpLeftCancellativeSemigroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftCancellativeSemigroupTerm n)) 
      opOL : ((OpLeftCancellativeSemigroupTerm n) → ((OpLeftCancellativeSemigroupTerm n) → (OpLeftCancellativeSemigroupTerm n)))  
      
  data OpLeftCancellativeSemigroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftCancellativeSemigroupTerm2 n A)) 
      sing2 : (A → (OpLeftCancellativeSemigroupTerm2 n A)) 
      opOL2 : ((OpLeftCancellativeSemigroupTerm2 n A) → ((OpLeftCancellativeSemigroupTerm2 n A) → (OpLeftCancellativeSemigroupTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLeftCancellativeSemigroupTerm A) → (ClLeftCancellativeSemigroupTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLeftCancellativeSemigroupTerm n) → (OpLeftCancellativeSemigroupTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLeftCancellativeSemigroupTerm2 n A) → (OpLeftCancellativeSemigroupTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftCancellativeSemigroup A) → (LeftCancellativeSemigroupTerm → A)) 
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftCancellativeSemigroup A) → ((ClLeftCancellativeSemigroupTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((LeftCancellativeSemigroup A) → ((Vec A n) → ((OpLeftCancellativeSemigroupTerm n) → A))) 
  evalOpB Le vars (v x1) = (lookup vars x1)  
  evalOpB Le vars (opOL x1 x2) = ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((LeftCancellativeSemigroup A) → ((Vec A n) → ((OpLeftCancellativeSemigroupTerm2 n A) → A))) 
  evalOp Le vars (v2 x1) = (lookup vars x1)  
  evalOp Le vars (sing2 x1) = x1  
  evalOp Le vars (opOL2 x1 x2) = ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  inductionB :  {P : (LeftCancellativeSemigroupTerm → Set)} →  (( (x1 x2 : LeftCancellativeSemigroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : LeftCancellativeSemigroupTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClLeftCancellativeSemigroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftCancellativeSemigroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClLeftCancellativeSemigroupTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLeftCancellativeSemigroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftCancellativeSemigroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpLeftCancellativeSemigroupTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLeftCancellativeSemigroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftCancellativeSemigroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpLeftCancellativeSemigroupTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (LeftCancellativeSemigroupTerm → (Staged LeftCancellativeSemigroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLeftCancellativeSemigroupTerm A) → (Staged (ClLeftCancellativeSemigroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLeftCancellativeSemigroupTerm n) → (Staged (OpLeftCancellativeSemigroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLeftCancellativeSemigroupTerm2 n A) → (Staged (OpLeftCancellativeSemigroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 