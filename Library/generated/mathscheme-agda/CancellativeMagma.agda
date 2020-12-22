
module CancellativeMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CancellativeMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      leftCancellative : ( {x y z : A} → ((op z x) ≡ (op z y) → x ≡ y)) 
      rightCancellative : ( {x y z : A} → ((op x z) ≡ (op y z) → x ≡ y))  
  
  open CancellativeMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP zP xP) ≡ (opP zP yP) → xP ≡ yP)) 
      rightCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP xP zP) ≡ (opP yP zP) → xP ≡ yP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ca1 : (CancellativeMagma A1)) (Ca2 : (CancellativeMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ca1) x1 x2)) ≡ ((op Ca2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ca1 : (CancellativeMagma A1)) (Ca2 : (CancellativeMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ca1) x1 x2) ((op Ca2) y1 y2)))))  
  
  data CancellativeMagmaTerm   : Set where 
      opL : (CancellativeMagmaTerm → (CancellativeMagmaTerm → CancellativeMagmaTerm))  
      
  data ClCancellativeMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClCancellativeMagmaTerm A)) 
      opCl : ((ClCancellativeMagmaTerm A) → ((ClCancellativeMagmaTerm A) → (ClCancellativeMagmaTerm A)))  
      
  data OpCancellativeMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCancellativeMagmaTerm n)) 
      opOL : ((OpCancellativeMagmaTerm n) → ((OpCancellativeMagmaTerm n) → (OpCancellativeMagmaTerm n)))  
      
  data OpCancellativeMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCancellativeMagmaTerm2 n A)) 
      sing2 : (A → (OpCancellativeMagmaTerm2 n A)) 
      opOL2 : ((OpCancellativeMagmaTerm2 n A) → ((OpCancellativeMagmaTerm2 n A) → (OpCancellativeMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClCancellativeMagmaTerm A) → (ClCancellativeMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpCancellativeMagmaTerm n) → (OpCancellativeMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpCancellativeMagmaTerm2 n A) → (OpCancellativeMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CancellativeMagma A) → (CancellativeMagmaTerm → A)) 
  evalB Ca (opL x1 x2) = ((op Ca) (evalB Ca x1) (evalB Ca x2))  
  evalCl :  {A : Set} →  ((CancellativeMagma A) → ((ClCancellativeMagmaTerm A) → A)) 
  evalCl Ca (sing x1) = x1  
  evalCl Ca (opCl x1 x2) = ((op Ca) (evalCl Ca x1) (evalCl Ca x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((CancellativeMagma A) → ((Vec A n) → ((OpCancellativeMagmaTerm n) → A))) 
  evalOpB n Ca vars (v x1) = (lookup vars x1)  
  evalOpB n Ca vars (opOL x1 x2) = ((op Ca) (evalOpB n Ca vars x1) (evalOpB n Ca vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((CancellativeMagma A) → ((Vec A n) → ((OpCancellativeMagmaTerm2 n A) → A))) 
  evalOp n Ca vars (v2 x1) = (lookup vars x1)  
  evalOp n Ca vars (sing2 x1) = x1  
  evalOp n Ca vars (opOL2 x1 x2) = ((op Ca) (evalOp n Ca vars x1) (evalOp n Ca vars x2))  
  inductionB :  (P : (CancellativeMagmaTerm → Set)) →  (( (x1 x2 : CancellativeMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : CancellativeMagmaTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClCancellativeMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCancellativeMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClCancellativeMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpCancellativeMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCancellativeMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpCancellativeMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpCancellativeMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCancellativeMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpCancellativeMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (CancellativeMagmaTerm → (Staged CancellativeMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClCancellativeMagmaTerm A) → (Staged (ClCancellativeMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpCancellativeMagmaTerm n) → (Staged (OpCancellativeMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpCancellativeMagmaTerm2 n A) → (Staged (OpCancellativeMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 