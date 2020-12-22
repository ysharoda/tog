
module Group   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsGroup  (A : Set) (e : A) (op : (A → (A → A))) (inv : (A → A)) : Set where 
     field  
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      leftInverse_inv_op_e : ( {x : A} → (op x (inv x)) ≡ e) 
      rightInverse_inv_op_e : ( {x : A} → (op (inv x) x) ≡ e)  
  
  record Group  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      inv : (A → A) 
      isGroup : (IsGroup A e op inv)  
  
  open Group
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS)) 
      invS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      invP : ((Prod A A) → (Prod A A)) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      leftInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP xP (invP xP)) ≡ eP) 
      rightInverse_inv_op_eP : ( {xP : (Prod A A)} → (opP (invP xP) xP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Gr1 : (Group A1)) (Gr2 : (Group A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Gr1)) ≡ (e Gr2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Gr1) x1 x2)) ≡ ((op Gr2) (hom x1) (hom x2))) 
      pres-inv : ( {x1 : A1} → (hom ((inv Gr1) x1)) ≡ ((inv Gr2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Gr1 : (Group A1)) (Gr2 : (Group A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Gr1) (e Gr2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Gr1) x1 x2) ((op Gr2) y1 y2))))) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Gr1) x1) ((inv Gr2) y1))))  
  
  data GroupTerm   : Set where 
      eL : GroupTerm 
      opL : (GroupTerm → (GroupTerm → GroupTerm)) 
      invL : (GroupTerm → GroupTerm)  
      
  data ClGroupTerm  (A : Set) : Set where 
      sing : (A → (ClGroupTerm A)) 
      eCl : (ClGroupTerm A) 
      opCl : ((ClGroupTerm A) → ((ClGroupTerm A) → (ClGroupTerm A))) 
      invCl : ((ClGroupTerm A) → (ClGroupTerm A))  
      
  data OpGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpGroupTerm n)) 
      eOL : (OpGroupTerm n) 
      opOL : ((OpGroupTerm n) → ((OpGroupTerm n) → (OpGroupTerm n))) 
      invOL : ((OpGroupTerm n) → (OpGroupTerm n))  
      
  data OpGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpGroupTerm2 n A)) 
      sing2 : (A → (OpGroupTerm2 n A)) 
      eOL2 : (OpGroupTerm2 n A) 
      opOL2 : ((OpGroupTerm2 n A) → ((OpGroupTerm2 n A) → (OpGroupTerm2 n A))) 
      invOL2 : ((OpGroupTerm2 n A) → (OpGroupTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClGroupTerm A) → (ClGroupTerm A)) 
  simplifyCl _ (opCl eCl x) = x  
  simplifyCl _ (opCl x eCl) = x  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (invCl x1) = (invCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpGroupTerm n) → (OpGroupTerm n)) 
  simplifyOpB _ (opOL eOL x) = x  
  simplifyOpB _ (opOL x eOL) = x  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (invOL x1) = (invOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpGroupTerm2 n A) → (OpGroupTerm2 n A)) 
  simplifyOp _ _ (opOL2 eOL2 x) = x  
  simplifyOp _ _ (opOL2 x eOL2) = x  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (invOL2 x1) = (invOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Group A) → (GroupTerm → A)) 
  evalB Gr eL = (e Gr)  
  evalB Gr (opL x1 x2) = ((op Gr) (evalB Gr x1) (evalB Gr x2))  
  evalB Gr (invL x1) = ((inv Gr) (evalB Gr x1))  
  evalCl :  {A : Set} →  ((Group A) → ((ClGroupTerm A) → A)) 
  evalCl Gr (sing x1) = x1  
  evalCl Gr eCl = (e Gr)  
  evalCl Gr (opCl x1 x2) = ((op Gr) (evalCl Gr x1) (evalCl Gr x2))  
  evalCl Gr (invCl x1) = ((inv Gr) (evalCl Gr x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((Group A) → ((Vec A n) → ((OpGroupTerm n) → A))) 
  evalOpB n Gr vars (v x1) = (lookup vars x1)  
  evalOpB n Gr vars eOL = (e Gr)  
  evalOpB n Gr vars (opOL x1 x2) = ((op Gr) (evalOpB n Gr vars x1) (evalOpB n Gr vars x2))  
  evalOpB n Gr vars (invOL x1) = ((inv Gr) (evalOpB n Gr vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((Group A) → ((Vec A n) → ((OpGroupTerm2 n A) → A))) 
  evalOp n Gr vars (v2 x1) = (lookup vars x1)  
  evalOp n Gr vars (sing2 x1) = x1  
  evalOp n Gr vars eOL2 = (e Gr)  
  evalOp n Gr vars (opOL2 x1 x2) = ((op Gr) (evalOp n Gr vars x1) (evalOp n Gr vars x2))  
  evalOp n Gr vars (invOL2 x1) = ((inv Gr) (evalOp n Gr vars x1))  
  inductionB :  (P : (GroupTerm → Set)) →  ((P eL) → (( (x1 x2 : GroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 : GroupTerm) → ((P x1) → (P (invL x1)))) → ( (x : GroupTerm) → (P x))))) 
  inductionB p pel popl pinvl eL = pel  
  inductionB p pel popl pinvl (opL x1 x2) = (popl _ _ (inductionB p pel popl pinvl x1) (inductionB p pel popl pinvl x2))  
  inductionB p pel popl pinvl (invL x1) = (pinvl _ (inductionB p pel popl pinvl x1))  
  inductionCl :  (A : Set) (P : ((ClGroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClGroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 : (ClGroupTerm A)) → ((P x1) → (P (invCl x1)))) → ( (x : (ClGroupTerm A)) → (P x)))))) 
  inductionCl _ p psing pecl popcl pinvcl (sing x1) = (psing x1)  
  inductionCl _ p psing pecl popcl pinvcl eCl = pecl  
  inductionCl _ p psing pecl popcl pinvcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl pinvcl x1) (inductionCl _ p psing pecl popcl pinvcl x2))  
  inductionCl _ p psing pecl popcl pinvcl (invCl x1) = (pinvcl _ (inductionCl _ p psing pecl popcl pinvcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpGroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpGroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 : (OpGroupTerm n)) → ((P x1) → (P (invOL x1)))) → ( (x : (OpGroupTerm n)) → (P x)))))) 
  inductionOpB _ p pv peol popol pinvol (v x1) = (pv x1)  
  inductionOpB _ p pv peol popol pinvol eOL = peol  
  inductionOpB _ p pv peol popol pinvol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol pinvol x1) (inductionOpB _ p pv peol popol pinvol x2))  
  inductionOpB _ p pv peol popol pinvol (invOL x1) = (pinvol _ (inductionOpB _ p pv peol popol pinvol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpGroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 : (OpGroupTerm2 n A)) → ((P x1) → (P (invOL2 x1)))) → ( (x : (OpGroupTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 x2))  
  inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 (invOL2 x1) = (pinvol2 _ (inductionOp _ _ p pv2 psing2 peol2 popol2 pinvol2 x1))  
  stageB :  (GroupTerm → (Staged GroupTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClGroupTerm A) → (Staged (ClGroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpGroupTerm n) → (Staged (OpGroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpGroupTerm2 n A) → (Staged (OpGroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      invT : ((Repr A) → (Repr A))  
  
 