
module CancellativeCommutativeMonoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCancellativeCommutativeMonoid  (A : Set) (op : (A → (A → A))) (e : A) : Set where 
     field  
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      leftCancellative : ( {x y z : A} → ((op z x) ≡ (op z y) → x ≡ y)) 
      rightCancellative : ( {x y z : A} → ((op x z) ≡ (op y z) → x ≡ y)) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x))  
  
  record CancellativeCommutativeMonoid  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      isCancellativeCommutativeMonoid : (IsCancellativeCommutativeMonoid A op e)  
  
  open CancellativeCommutativeMonoid
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
      leftCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP zP xP) ≡ (opP zP yP) → xP ≡ yP)) 
      rightCancellativeP : ( {xP yP zP : (Prod A A)} → ((opP xP zP) ≡ (opP yP zP) → xP ≡ yP)) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ca1 : (CancellativeCommutativeMonoid A1)) (Ca2 : (CancellativeCommutativeMonoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ca1) x1 x2)) ≡ ((op Ca2) (hom x1) (hom x2))) 
      pres-e : (hom (e Ca1)) ≡ (e Ca2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ca1 : (CancellativeCommutativeMonoid A1)) (Ca2 : (CancellativeCommutativeMonoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ca1) x1 x2) ((op Ca2) y1 y2))))) 
      interp-e : (interp (e Ca1) (e Ca2))  
  
  data CancellativeCommutativeMonoidTerm   : Set where 
      opL : (CancellativeCommutativeMonoidTerm → (CancellativeCommutativeMonoidTerm → CancellativeCommutativeMonoidTerm)) 
      eL : CancellativeCommutativeMonoidTerm  
      
  data ClCancellativeCommutativeMonoidTerm  (A : Set) : Set where 
      sing : (A → (ClCancellativeCommutativeMonoidTerm A)) 
      opCl : ((ClCancellativeCommutativeMonoidTerm A) → ((ClCancellativeCommutativeMonoidTerm A) → (ClCancellativeCommutativeMonoidTerm A))) 
      eCl : (ClCancellativeCommutativeMonoidTerm A)  
      
  data OpCancellativeCommutativeMonoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCancellativeCommutativeMonoidTerm n)) 
      opOL : ((OpCancellativeCommutativeMonoidTerm n) → ((OpCancellativeCommutativeMonoidTerm n) → (OpCancellativeCommutativeMonoidTerm n))) 
      eOL : (OpCancellativeCommutativeMonoidTerm n)  
      
  data OpCancellativeCommutativeMonoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCancellativeCommutativeMonoidTerm2 n A)) 
      sing2 : (A → (OpCancellativeCommutativeMonoidTerm2 n A)) 
      opOL2 : ((OpCancellativeCommutativeMonoidTerm2 n A) → ((OpCancellativeCommutativeMonoidTerm2 n A) → (OpCancellativeCommutativeMonoidTerm2 n A))) 
      eOL2 : (OpCancellativeCommutativeMonoidTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClCancellativeCommutativeMonoidTerm A) → (ClCancellativeCommutativeMonoidTerm A)) 
  simplifyCl (opCl eCl x) = x  
  simplifyCl (opCl x eCl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpCancellativeCommutativeMonoidTerm n) → (OpCancellativeCommutativeMonoidTerm n)) 
  simplifyOpB (opOL eOL x) = x  
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpCancellativeCommutativeMonoidTerm2 n A) → (OpCancellativeCommutativeMonoidTerm2 n A)) 
  simplifyOp (opOL2 eOL2 x) = x  
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CancellativeCommutativeMonoid A) → (CancellativeCommutativeMonoidTerm → A)) 
  evalB Ca (opL x1 x2) = ((op Ca) (evalB Ca x1) (evalB Ca x2))  
  evalB Ca eL = (e Ca)  
  evalCl :  {A : Set} →  ((CancellativeCommutativeMonoid A) → ((ClCancellativeCommutativeMonoidTerm A) → A)) 
  evalCl Ca (sing x1) = x1  
  evalCl Ca (opCl x1 x2) = ((op Ca) (evalCl Ca x1) (evalCl Ca x2))  
  evalCl Ca eCl = (e Ca)  
  evalOpB :  {A : Set} {n : Nat} →  ((CancellativeCommutativeMonoid A) → ((Vec A n) → ((OpCancellativeCommutativeMonoidTerm n) → A))) 
  evalOpB Ca vars (v x1) = (lookup vars x1)  
  evalOpB Ca vars (opOL x1 x2) = ((op Ca) (evalOpB Ca vars x1) (evalOpB Ca vars x2))  
  evalOpB Ca vars eOL = (e Ca)  
  evalOp :  {A : Set} {n : Nat} →  ((CancellativeCommutativeMonoid A) → ((Vec A n) → ((OpCancellativeCommutativeMonoidTerm2 n A) → A))) 
  evalOp Ca vars (v2 x1) = (lookup vars x1)  
  evalOp Ca vars (sing2 x1) = x1  
  evalOp Ca vars (opOL2 x1 x2) = ((op Ca) (evalOp Ca vars x1) (evalOp Ca vars x2))  
  evalOp Ca vars eOL2 = (e Ca)  
  inductionB :  {P : (CancellativeCommutativeMonoidTerm → Set)} →  (( (x1 x2 : CancellativeCommutativeMonoidTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : CancellativeCommutativeMonoidTerm) → (P x)))) 
  inductionB popl pel (opL x1 x2) = (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  inductionB popl pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClCancellativeCommutativeMonoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCancellativeCommutativeMonoidTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClCancellativeCommutativeMonoidTerm A)) → (P x))))) 
  inductionCl psing popcl pecl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  inductionCl psing popcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpCancellativeCommutativeMonoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCancellativeCommutativeMonoidTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpCancellativeCommutativeMonoidTerm n)) → (P x))))) 
  inductionOpB pv popol peol (v x1) = (pv x1)  
  inductionOpB pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  inductionOpB pv popol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpCancellativeCommutativeMonoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCancellativeCommutativeMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpCancellativeCommutativeMonoidTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (CancellativeCommutativeMonoidTerm → (Staged CancellativeCommutativeMonoidTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClCancellativeCommutativeMonoidTerm A) → (Staged (ClCancellativeCommutativeMonoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpCancellativeCommutativeMonoidTerm n) → (Staged (OpCancellativeCommutativeMonoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpCancellativeCommutativeMonoidTerm2 n A) → (Staged (OpCancellativeCommutativeMonoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 