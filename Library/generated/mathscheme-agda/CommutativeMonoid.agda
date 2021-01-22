
module CommutativeMonoid   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeMonoid  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      e : A 
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x))  
  
  open CommutativeMonoid
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (CommutativeMonoid A1)) (Co2 : (CommutativeMonoid A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Co1) x1 x2)) ≡ ((op Co2) (hom x1) (hom x2))) 
      pres-e : (hom (e Co1)) ≡ (e Co2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (CommutativeMonoid A1)) (Co2 : (CommutativeMonoid A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))) 
      interp-e : (interp (e Co1) (e Co2))  
  
  data CommutativeMonoidTerm   : Set where 
      opL : (CommutativeMonoidTerm → (CommutativeMonoidTerm → CommutativeMonoidTerm)) 
      eL : CommutativeMonoidTerm  
      
  data ClCommutativeMonoidTerm  (A : Set) : Set where 
      sing : (A → (ClCommutativeMonoidTerm A)) 
      opCl : ((ClCommutativeMonoidTerm A) → ((ClCommutativeMonoidTerm A) → (ClCommutativeMonoidTerm A))) 
      eCl : (ClCommutativeMonoidTerm A)  
      
  data OpCommutativeMonoidTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCommutativeMonoidTerm n)) 
      opOL : ((OpCommutativeMonoidTerm n) → ((OpCommutativeMonoidTerm n) → (OpCommutativeMonoidTerm n))) 
      eOL : (OpCommutativeMonoidTerm n)  
      
  data OpCommutativeMonoidTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCommutativeMonoidTerm2 n A)) 
      sing2 : (A → (OpCommutativeMonoidTerm2 n A)) 
      opOL2 : ((OpCommutativeMonoidTerm2 n A) → ((OpCommutativeMonoidTerm2 n A) → (OpCommutativeMonoidTerm2 n A))) 
      eOL2 : (OpCommutativeMonoidTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClCommutativeMonoidTerm A) → (ClCommutativeMonoidTerm A)) 
  simplifyCl (opCl eCl x) = x  
  simplifyCl (opCl x eCl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpCommutativeMonoidTerm n) → (OpCommutativeMonoidTerm n)) 
  simplifyOpB (opOL eOL x) = x  
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpCommutativeMonoidTerm2 n A) → (OpCommutativeMonoidTerm2 n A)) 
  simplifyOp (opOL2 eOL2 x) = x  
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativeMonoid A) → (CommutativeMonoidTerm → A)) 
  evalB Co (opL x1 x2) = ((op Co) (evalB Co x1) (evalB Co x2))  
  evalB Co eL = (e Co)  
  evalCl :  {A : Set} →  ((CommutativeMonoid A) → ((ClCommutativeMonoidTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (opCl x1 x2) = ((op Co) (evalCl Co x1) (evalCl Co x2))  
  evalCl Co eCl = (e Co)  
  evalOpB :  {A : Set} {n : Nat} →  ((CommutativeMonoid A) → ((Vec A n) → ((OpCommutativeMonoidTerm n) → A))) 
  evalOpB Co vars (v x1) = (lookup vars x1)  
  evalOpB Co vars (opOL x1 x2) = ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  evalOpB Co vars eOL = (e Co)  
  evalOp :  {A : Set} {n : Nat} →  ((CommutativeMonoid A) → ((Vec A n) → ((OpCommutativeMonoidTerm2 n A) → A))) 
  evalOp Co vars (v2 x1) = (lookup vars x1)  
  evalOp Co vars (sing2 x1) = x1  
  evalOp Co vars (opOL2 x1 x2) = ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  evalOp Co vars eOL2 = (e Co)  
  inductionB :  {P : (CommutativeMonoidTerm → Set)} →  (( (x1 x2 : CommutativeMonoidTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : CommutativeMonoidTerm) → (P x)))) 
  inductionB popl pel (opL x1 x2) = (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  inductionB popl pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClCommutativeMonoidTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativeMonoidTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClCommutativeMonoidTerm A)) → (P x))))) 
  inductionCl psing popcl pecl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  inductionCl psing popcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpCommutativeMonoidTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativeMonoidTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpCommutativeMonoidTerm n)) → (P x))))) 
  inductionOpB pv popol peol (v x1) = (pv x1)  
  inductionOpB pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  inductionOpB pv popol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpCommutativeMonoidTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativeMonoidTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpCommutativeMonoidTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (CommutativeMonoidTerm → (Staged CommutativeMonoidTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClCommutativeMonoidTerm A) → (Staged (ClCommutativeMonoidTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpCommutativeMonoidTerm n) → (Staged (OpCommutativeMonoidTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpCommutativeMonoidTerm2 n A) → (Staged (OpCommutativeMonoidTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 