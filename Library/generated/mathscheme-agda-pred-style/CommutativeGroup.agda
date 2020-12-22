
module CommutativeGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCommutativeGroup  (A : Set) (op : (A → (A → A))) (e : A) (inv : (A → A)) : Set where 
     field  
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      leftInverse_inv_op_e : ( {x : A} → (op x (inv x)) ≡ e) 
      rightInverse_inv_op_e : ( {x : A} → (op (inv x) x) ≡ e) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x))  
  
  record CommutativeGroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      inv : (A → A) 
      isCommutativeGroup : (IsCommutativeGroup A op e inv)  
  
  open CommutativeGroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS 
      invS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      invP : ((Prod A A) → (Prod A A)) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      leftInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP xP (invP xP)) ≡ eP) 
      rightInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP (invP xP) xP) ≡ eP) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (CommutativeGroup A1)) (Co2 : (CommutativeGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Co1) x1 x2)) ≡ ((op Co2) (hom x1) (hom x2))) 
      pres-e : (hom (e Co1)) ≡ (e Co2) 
      pres-inv : ( {x1 : A1} → (hom ((inv Co1) x1)) ≡ ((inv Co2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (CommutativeGroup A1)) (Co2 : (CommutativeGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))) 
      interp-e : (interp (e Co1) (e Co2)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Co1) x1) ((inv Co2) y1))))  
  
  data CommutativeGroupTerm   : Set where 
      opL : (CommutativeGroupTerm → (CommutativeGroupTerm → CommutativeGroupTerm)) 
      eL : CommutativeGroupTerm 
      invL : (CommutativeGroupTerm → CommutativeGroupTerm)  
      
  data ClCommutativeGroupTerm  (A : Set) : Set where 
      sing : (A → (ClCommutativeGroupTerm A)) 
      opCl : ((ClCommutativeGroupTerm A) → ((ClCommutativeGroupTerm A) → (ClCommutativeGroupTerm A))) 
      eCl : (ClCommutativeGroupTerm A) 
      invCl : ((ClCommutativeGroupTerm A) → (ClCommutativeGroupTerm A))  
      
  data OpCommutativeGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCommutativeGroupTerm n)) 
      opOL : ((OpCommutativeGroupTerm n) → ((OpCommutativeGroupTerm n) → (OpCommutativeGroupTerm n))) 
      eOL : (OpCommutativeGroupTerm n) 
      invOL : ((OpCommutativeGroupTerm n) → (OpCommutativeGroupTerm n))  
      
  data OpCommutativeGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCommutativeGroupTerm2 n A)) 
      sing2 : (A → (OpCommutativeGroupTerm2 n A)) 
      opOL2 : ((OpCommutativeGroupTerm2 n A) → ((OpCommutativeGroupTerm2 n A) → (OpCommutativeGroupTerm2 n A))) 
      eOL2 : (OpCommutativeGroupTerm2 n A) 
      invOL2 : ((OpCommutativeGroupTerm2 n A) → (OpCommutativeGroupTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClCommutativeGroupTerm A) → (ClCommutativeGroupTerm A)) 
  simplifyCl _ (opCl eCl x) = x  
  simplifyCl _ (opCl x eCl) = x  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (invCl x1) = (invCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpCommutativeGroupTerm n) → (OpCommutativeGroupTerm n)) 
  simplifyOpB _ (opOL eOL x) = x  
  simplifyOpB _ (opOL x eOL) = x  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (invOL x1) = (invOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpCommutativeGroupTerm2 n A) → (OpCommutativeGroupTerm2 n A)) 
  simplifyOp _ _ (opOL2 eOL2 x) = x  
  simplifyOp _ _ (opOL2 x eOL2) = x  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (invOL2 x1) = (invOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativeGroup A) → (CommutativeGroupTerm → A)) 
  evalB Co (opL x1 x2) = ((op Co) (evalB Co x1) (evalB Co x2))  
  evalB Co eL = (e Co)  
  evalB Co (invL x1) = ((inv Co) (evalB Co x1))  
  evalCl :  {A : Set} →  ((CommutativeGroup A) → ((ClCommutativeGroupTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (opCl x1 x2) = ((op Co) (evalCl Co x1) (evalCl Co x2))  
  evalCl Co eCl = (e Co)  
  evalCl Co (invCl x1) = ((inv Co) (evalCl Co x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((CommutativeGroup A) → ((Vec A n) → ((OpCommutativeGroupTerm n) → A))) 
  evalOpB n Co vars (v x1) = (lookup vars x1)  
  evalOpB n Co vars (opOL x1 x2) = ((op Co) (evalOpB n Co vars x1) (evalOpB n Co vars x2))  
  evalOpB n Co vars eOL = (e Co)  
  evalOpB n Co vars (invOL x1) = ((inv Co) (evalOpB n Co vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((CommutativeGroup A) → ((Vec A n) → ((OpCommutativeGroupTerm2 n A) → A))) 
  evalOp n Co vars (v2 x1) = (lookup vars x1)  
  evalOp n Co vars (sing2 x1) = x1  
  evalOp n Co vars (opOL2 x1 x2) = ((op Co) (evalOp n Co vars x1) (evalOp n Co vars x2))  
  evalOp n Co vars eOL2 = (e Co)  
  evalOp n Co vars (invOL2 x1) = ((inv Co) (evalOp n Co vars x1))  
  inductionB :  (P : (CommutativeGroupTerm → Set)) →  (( (x1 x2 : CommutativeGroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (( (x1 : CommutativeGroupTerm) → ((P x1) → (P (invL x1)))) → ( (x : CommutativeGroupTerm) → (P x))))) 
  inductionB p popl pel pinvl (opL x1 x2) = (popl _ _ (inductionB p popl pel pinvl x1) (inductionB p popl pel pinvl x2))  
  inductionB p popl pel pinvl eL = pel  
  inductionB p popl pel pinvl (invL x1) = (pinvl _ (inductionB p popl pel pinvl x1))  
  inductionCl :  (A : Set) (P : ((ClCommutativeGroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativeGroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (( (x1 : (ClCommutativeGroupTerm A)) → ((P x1) → (P (invCl x1)))) → ( (x : (ClCommutativeGroupTerm A)) → (P x)))))) 
  inductionCl _ p psing popcl pecl pinvcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl pecl pinvcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl pecl pinvcl x1) (inductionCl _ p psing popcl pecl pinvcl x2))  
  inductionCl _ p psing popcl pecl pinvcl eCl = pecl  
  inductionCl _ p psing popcl pecl pinvcl (invCl x1) = (pinvcl _ (inductionCl _ p psing popcl pecl pinvcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpCommutativeGroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativeGroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (( (x1 : (OpCommutativeGroupTerm n)) → ((P x1) → (P (invOL x1)))) → ( (x : (OpCommutativeGroupTerm n)) → (P x)))))) 
  inductionOpB _ p pv popol peol pinvol (v x1) = (pv x1)  
  inductionOpB _ p pv popol peol pinvol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol peol pinvol x1) (inductionOpB _ p pv popol peol pinvol x2))  
  inductionOpB _ p pv popol peol pinvol eOL = peol  
  inductionOpB _ p pv popol peol pinvol (invOL x1) = (pinvol _ (inductionOpB _ p pv popol peol pinvol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpCommutativeGroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativeGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (( (x1 : (OpCommutativeGroupTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → ( (x : (OpCommutativeGroupTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 (invOL2 x1) = (pinvol2 _ (inductionOp _ _ p pv2 psing2 popol2 peol2 pinvol2 x1))  
  stageB :  (CommutativeGroupTerm → (Staged CommutativeGroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClCommutativeGroupTerm A) → (Staged (ClCommutativeGroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpCommutativeGroupTerm n) → (Staged (OpCommutativeGroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpCommutativeGroupTerm2 n A) → (Staged (OpCommutativeGroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A) 
      invT : ((Repr A) → (Repr A))  
  
 