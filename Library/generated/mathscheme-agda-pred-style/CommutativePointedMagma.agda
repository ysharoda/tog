
module CommutativePointedMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCommutativePointedMagma  (A : Set) (op : (A → (A → A))) (e : A) : Set where 
     field  
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x))  
  
  record CommutativePointedMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      isCommutativePointedMagma : (IsCommutativePointedMagma A op e)  
  
  open CommutativePointedMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (CommutativePointedMagma A1)) (Co2 : (CommutativePointedMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Co1) x1 x2)) ≡ ((op Co2) (hom x1) (hom x2))) 
      pres-e : (hom (e Co1)) ≡ (e Co2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (CommutativePointedMagma A1)) (Co2 : (CommutativePointedMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))) 
      interp-e : (interp (e Co1) (e Co2))  
  
  data CommutativePointedMagmaTerm   : Set where 
      opL : (CommutativePointedMagmaTerm → (CommutativePointedMagmaTerm → CommutativePointedMagmaTerm)) 
      eL : CommutativePointedMagmaTerm  
      
  data ClCommutativePointedMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClCommutativePointedMagmaTerm A)) 
      opCl : ((ClCommutativePointedMagmaTerm A) → ((ClCommutativePointedMagmaTerm A) → (ClCommutativePointedMagmaTerm A))) 
      eCl : (ClCommutativePointedMagmaTerm A)  
      
  data OpCommutativePointedMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCommutativePointedMagmaTerm n)) 
      opOL : ((OpCommutativePointedMagmaTerm n) → ((OpCommutativePointedMagmaTerm n) → (OpCommutativePointedMagmaTerm n))) 
      eOL : (OpCommutativePointedMagmaTerm n)  
      
  data OpCommutativePointedMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCommutativePointedMagmaTerm2 n A)) 
      sing2 : (A → (OpCommutativePointedMagmaTerm2 n A)) 
      opOL2 : ((OpCommutativePointedMagmaTerm2 n A) → ((OpCommutativePointedMagmaTerm2 n A) → (OpCommutativePointedMagmaTerm2 n A))) 
      eOL2 : (OpCommutativePointedMagmaTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClCommutativePointedMagmaTerm A) → (ClCommutativePointedMagmaTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpCommutativePointedMagmaTerm n) → (OpCommutativePointedMagmaTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpCommutativePointedMagmaTerm2 n A) → (OpCommutativePointedMagmaTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativePointedMagma A) → (CommutativePointedMagmaTerm → A)) 
  evalB Co (opL x1 x2) = ((op Co) (evalB Co x1) (evalB Co x2))  
  evalB Co eL = (e Co)  
  evalCl :  {A : Set} →  ((CommutativePointedMagma A) → ((ClCommutativePointedMagmaTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (opCl x1 x2) = ((op Co) (evalCl Co x1) (evalCl Co x2))  
  evalCl Co eCl = (e Co)  
  evalOpB :  {A : Set} {n : Nat} →  ((CommutativePointedMagma A) → ((Vec A n) → ((OpCommutativePointedMagmaTerm n) → A))) 
  evalOpB Co vars (v x1) = (lookup vars x1)  
  evalOpB Co vars (opOL x1 x2) = ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  evalOpB Co vars eOL = (e Co)  
  evalOp :  {A : Set} {n : Nat} →  ((CommutativePointedMagma A) → ((Vec A n) → ((OpCommutativePointedMagmaTerm2 n A) → A))) 
  evalOp Co vars (v2 x1) = (lookup vars x1)  
  evalOp Co vars (sing2 x1) = x1  
  evalOp Co vars (opOL2 x1 x2) = ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  evalOp Co vars eOL2 = (e Co)  
  inductionB :  {P : (CommutativePointedMagmaTerm → Set)} →  (( (x1 x2 : CommutativePointedMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ( (x : CommutativePointedMagmaTerm) → (P x)))) 
  inductionB popl pel (opL x1 x2) = (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  inductionB popl pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClCommutativePointedMagmaTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativePointedMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ( (x : (ClCommutativePointedMagmaTerm A)) → (P x))))) 
  inductionCl psing popcl pecl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  inductionCl psing popcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpCommutativePointedMagmaTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativePointedMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ( (x : (OpCommutativePointedMagmaTerm n)) → (P x))))) 
  inductionOpB pv popol peol (v x1) = (pv x1)  
  inductionOpB pv popol peol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  inductionOpB pv popol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpCommutativePointedMagmaTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativePointedMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ( (x : (OpCommutativePointedMagmaTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 eOL2 = peol2  
  stageB :  (CommutativePointedMagmaTerm → (Staged CommutativePointedMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClCommutativePointedMagmaTerm A) → (Staged (ClCommutativePointedMagmaTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpCommutativePointedMagmaTerm n) → (Staged (OpCommutativePointedMagmaTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpCommutativePointedMagmaTerm2 n A) → (Staged (OpCommutativePointedMagmaTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A)  
  
 