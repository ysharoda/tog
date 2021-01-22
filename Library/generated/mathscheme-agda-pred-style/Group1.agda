
module Group1   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsGroup1  (A : Set) (op : (A → (A → A))) (1ᵢ : A) (inv : (A → A)) : Set where 
     field  
      lunit_1ᵢ : ( {x : A} → (op 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (op x 1ᵢ) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      leftInverse_inv_op_1ᵢ : ( {x : A} → (op x (inv x)) ≡ 1ᵢ) 
      rightInverse_inv_op_1ᵢ : ( {x : A} → (op (inv x) x) ≡ 1ᵢ)  
  
  record Group1  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      1ᵢ : A 
      inv : (A → A) 
      isGroup1 : (IsGroup1 A op 1ᵢ inv)  
  
  open Group1
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      1S : AS 
      invS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      invP : ((Prod A A) → (Prod A A)) 
      lunit_1P : ( {xP : (Prod A A)} → (opP 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (opP xP 1P) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      leftInverse_inv_op_1P : ( {xP : (Prod A A)} → (opP xP (invP xP)) ≡ 1P) 
      rightInverse_inv_op_1P : ( {xP : (Prod A A)} → (opP (invP xP) xP) ≡ 1P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Gr1 : (Group1 A1)) (Gr2 : (Group1 A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Gr1) x1 x2)) ≡ ((op Gr2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Gr1)) ≡ (1ᵢ Gr2) 
      pres-inv : ( {x1 : A1} → (hom ((inv Gr1) x1)) ≡ ((inv Gr2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Gr1 : (Group1 A1)) (Gr2 : (Group1 A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Gr1) x1 x2) ((op Gr2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Gr1) (1ᵢ Gr2)) 
      interp-inv : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv Gr1) x1) ((inv Gr2) y1))))  
  
  data Group1LTerm   : Set where 
      opL : (Group1LTerm → (Group1LTerm → Group1LTerm)) 
      1L : Group1LTerm 
      invL : (Group1LTerm → Group1LTerm)  
      
  data ClGroup1ClTerm  (A : Set) : Set where 
      sing : (A → (ClGroup1ClTerm A)) 
      opCl : ((ClGroup1ClTerm A) → ((ClGroup1ClTerm A) → (ClGroup1ClTerm A))) 
      1Cl : (ClGroup1ClTerm A) 
      invCl : ((ClGroup1ClTerm A) → (ClGroup1ClTerm A))  
      
  data OpGroup1OLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpGroup1OLTerm n)) 
      opOL : ((OpGroup1OLTerm n) → ((OpGroup1OLTerm n) → (OpGroup1OLTerm n))) 
      1OL : (OpGroup1OLTerm n) 
      invOL : ((OpGroup1OLTerm n) → (OpGroup1OLTerm n))  
      
  data OpGroup1OL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpGroup1OL2Term2 n A)) 
      sing2 : (A → (OpGroup1OL2Term2 n A)) 
      opOL2 : ((OpGroup1OL2Term2 n A) → ((OpGroup1OL2Term2 n A) → (OpGroup1OL2Term2 n A))) 
      1OL2 : (OpGroup1OL2Term2 n A) 
      invOL2 : ((OpGroup1OL2Term2 n A) → (OpGroup1OL2Term2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClGroup1ClTerm A) → (ClGroup1ClTerm A)) 
  simplifyCl (opCl 1Cl x) = x  
  simplifyCl (opCl x 1Cl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (invCl x1) = (invCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpGroup1OLTerm n) → (OpGroup1OLTerm n)) 
  simplifyOpB (opOL 1OL x) = x  
  simplifyOpB (opOL x 1OL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (invOL x1) = (invOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpGroup1OL2Term2 n A) → (OpGroup1OL2Term2 n A)) 
  simplifyOp (opOL2 1OL2 x) = x  
  simplifyOp (opOL2 x 1OL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (invOL2 x1) = (invOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Group1 A) → (Group1LTerm → A)) 
  evalB Gr (opL x1 x2) = ((op Gr) (evalB Gr x1) (evalB Gr x2))  
  evalB Gr 1L = (1ᵢ Gr)  
  evalB Gr (invL x1) = ((inv Gr) (evalB Gr x1))  
  evalCl :  {A : Set} →  ((Group1 A) → ((ClGroup1ClTerm A) → A)) 
  evalCl Gr (sing x1) = x1  
  evalCl Gr (opCl x1 x2) = ((op Gr) (evalCl Gr x1) (evalCl Gr x2))  
  evalCl Gr 1Cl = (1ᵢ Gr)  
  evalCl Gr (invCl x1) = ((inv Gr) (evalCl Gr x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((Group1 A) → ((Vec A n) → ((OpGroup1OLTerm n) → A))) 
  evalOpB Gr vars (v x1) = (lookup vars x1)  
  evalOpB Gr vars (opOL x1 x2) = ((op Gr) (evalOpB Gr vars x1) (evalOpB Gr vars x2))  
  evalOpB Gr vars 1OL = (1ᵢ Gr)  
  evalOpB Gr vars (invOL x1) = ((inv Gr) (evalOpB Gr vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((Group1 A) → ((Vec A n) → ((OpGroup1OL2Term2 n A) → A))) 
  evalOp Gr vars (v2 x1) = (lookup vars x1)  
  evalOp Gr vars (sing2 x1) = x1  
  evalOp Gr vars (opOL2 x1 x2) = ((op Gr) (evalOp Gr vars x1) (evalOp Gr vars x2))  
  evalOp Gr vars 1OL2 = (1ᵢ Gr)  
  evalOp Gr vars (invOL2 x1) = ((inv Gr) (evalOp Gr vars x1))  
  inductionB :  {P : (Group1LTerm → Set)} →  (( (x1 x2 : Group1LTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P 1L) → (( (x1 : Group1LTerm) → ((P x1) → (P (invL x1)))) → ( (x : Group1LTerm) → (P x))))) 
  inductionB popl p1l pinvl (opL x1 x2) = (popl _ _ (inductionB popl p1l pinvl x1) (inductionB popl p1l pinvl x2))  
  inductionB popl p1l pinvl 1L = p1l  
  inductionB popl p1l pinvl (invL x1) = (pinvl _ (inductionB popl p1l pinvl x1))  
  inductionCl :  {A : Set} {P : ((ClGroup1ClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClGroup1ClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P 1Cl) → (( (x1 : (ClGroup1ClTerm A)) → ((P x1) → (P (invCl x1)))) → ( (x : (ClGroup1ClTerm A)) → (P x)))))) 
  inductionCl psing popcl p1cl pinvcl (sing x1) = (psing x1)  
  inductionCl psing popcl p1cl pinvcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl p1cl pinvcl x1) (inductionCl psing popcl p1cl pinvcl x2))  
  inductionCl psing popcl p1cl pinvcl 1Cl = p1cl  
  inductionCl psing popcl p1cl pinvcl (invCl x1) = (pinvcl _ (inductionCl psing popcl p1cl pinvcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpGroup1OLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpGroup1OLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P 1OL) → (( (x1 : (OpGroup1OLTerm n)) → ((P x1) → (P (invOL x1)))) → ( (x : (OpGroup1OLTerm n)) → (P x)))))) 
  inductionOpB pv popol p1ol pinvol (v x1) = (pv x1)  
  inductionOpB pv popol p1ol pinvol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol p1ol pinvol x1) (inductionOpB pv popol p1ol pinvol x2))  
  inductionOpB pv popol p1ol pinvol 1OL = p1ol  
  inductionOpB pv popol p1ol pinvol (invOL x1) = (pinvol _ (inductionOpB pv popol p1ol pinvol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpGroup1OL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpGroup1OL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P 1OL2) → (( (x1 : (OpGroup1OL2Term2 n A)) → ((P x1) → (P (invOL2 x1)))) → ( (x : (OpGroup1OL2Term2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 popol2 p1ol2 pinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 p1ol2 pinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 p1ol2 pinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 p1ol2 pinvol2 x1) (inductionOp pv2 psing2 popol2 p1ol2 pinvol2 x2))  
  inductionOp pv2 psing2 popol2 p1ol2 pinvol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 popol2 p1ol2 pinvol2 (invOL2 x1) = (pinvol2 _ (inductionOp pv2 psing2 popol2 p1ol2 pinvol2 x1))  
  stageB :  (Group1LTerm → (Staged Group1LTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (invL x1) = (stage1 invL (codeLift1 invL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClGroup1ClTerm A) → (Staged (ClGroup1ClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (invCl x1) = (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpGroup1OLTerm n) → (Staged (OpGroup1OLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (invOL x1) = (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpGroup1OL2Term2 n A) → (Staged (OpGroup1OL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (invOL2 x1) = (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      invT : ((Repr A) → (Repr A))  
  
 