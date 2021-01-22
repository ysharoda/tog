
module CommutativeMonoid1   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCommutativeMonoid1  (A : Set) (op : (A → (A → A))) (1ᵢ : A) : Set where 
     field  
      lunit_1ᵢ : ( {x : A} → (op 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (op x 1ᵢ) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x))  
  
  record CommutativeMonoid1  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      1ᵢ : A 
      isCommutativeMonoid1 : (IsCommutativeMonoid1 A op 1ᵢ)  
  
  open CommutativeMonoid1
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      lunit_1P : ( {xP : (Prod A A)} → (opP 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (opP xP 1P) ≡ xP) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (CommutativeMonoid1 A1)) (Co2 : (CommutativeMonoid1 A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Co1) x1 x2)) ≡ ((op Co2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ Co1)) ≡ (1ᵢ Co2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (CommutativeMonoid1 A1)) (Co2 : (CommutativeMonoid1 A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))) 
      interp-1 : (interp (1ᵢ Co1) (1ᵢ Co2))  
  
  data CommutativeMonoid1LTerm   : Set where 
      opL : (CommutativeMonoid1LTerm → (CommutativeMonoid1LTerm → CommutativeMonoid1LTerm)) 
      1L : CommutativeMonoid1LTerm  
      
  data ClCommutativeMonoid1ClTerm  (A : Set) : Set where 
      sing : (A → (ClCommutativeMonoid1ClTerm A)) 
      opCl : ((ClCommutativeMonoid1ClTerm A) → ((ClCommutativeMonoid1ClTerm A) → (ClCommutativeMonoid1ClTerm A))) 
      1Cl : (ClCommutativeMonoid1ClTerm A)  
      
  data OpCommutativeMonoid1OLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCommutativeMonoid1OLTerm n)) 
      opOL : ((OpCommutativeMonoid1OLTerm n) → ((OpCommutativeMonoid1OLTerm n) → (OpCommutativeMonoid1OLTerm n))) 
      1OL : (OpCommutativeMonoid1OLTerm n)  
      
  data OpCommutativeMonoid1OL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCommutativeMonoid1OL2Term2 n A)) 
      sing2 : (A → (OpCommutativeMonoid1OL2Term2 n A)) 
      opOL2 : ((OpCommutativeMonoid1OL2Term2 n A) → ((OpCommutativeMonoid1OL2Term2 n A) → (OpCommutativeMonoid1OL2Term2 n A))) 
      1OL2 : (OpCommutativeMonoid1OL2Term2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClCommutativeMonoid1ClTerm A) → (ClCommutativeMonoid1ClTerm A)) 
  simplifyCl (opCl 1Cl x) = x  
  simplifyCl (opCl x 1Cl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpCommutativeMonoid1OLTerm n) → (OpCommutativeMonoid1OLTerm n)) 
  simplifyOpB (opOL 1OL x) = x  
  simplifyOpB (opOL x 1OL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpCommutativeMonoid1OL2Term2 n A) → (OpCommutativeMonoid1OL2Term2 n A)) 
  simplifyOp (opOL2 1OL2 x) = x  
  simplifyOp (opOL2 x 1OL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativeMonoid1 A) → (CommutativeMonoid1LTerm → A)) 
  evalB Co (opL x1 x2) = ((op Co) (evalB Co x1) (evalB Co x2))  
  evalB Co 1L = (1ᵢ Co)  
  evalCl :  {A : Set} →  ((CommutativeMonoid1 A) → ((ClCommutativeMonoid1ClTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (opCl x1 x2) = ((op Co) (evalCl Co x1) (evalCl Co x2))  
  evalCl Co 1Cl = (1ᵢ Co)  
  evalOpB :  {A : Set} {n : Nat} →  ((CommutativeMonoid1 A) → ((Vec A n) → ((OpCommutativeMonoid1OLTerm n) → A))) 
  evalOpB Co vars (v x1) = (lookup vars x1)  
  evalOpB Co vars (opOL x1 x2) = ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  evalOpB Co vars 1OL = (1ᵢ Co)  
  evalOp :  {A : Set} {n : Nat} →  ((CommutativeMonoid1 A) → ((Vec A n) → ((OpCommutativeMonoid1OL2Term2 n A) → A))) 
  evalOp Co vars (v2 x1) = (lookup vars x1)  
  evalOp Co vars (sing2 x1) = x1  
  evalOp Co vars (opOL2 x1 x2) = ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  evalOp Co vars 1OL2 = (1ᵢ Co)  
  inductionB :  {P : (CommutativeMonoid1LTerm → Set)} →  (( (x1 x2 : CommutativeMonoid1LTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P 1L) → ( (x : CommutativeMonoid1LTerm) → (P x)))) 
  inductionB popl p1l (opL x1 x2) = (popl _ _ (inductionB popl p1l x1) (inductionB popl p1l x2))  
  inductionB popl p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClCommutativeMonoid1ClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativeMonoid1ClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P 1Cl) → ( (x : (ClCommutativeMonoid1ClTerm A)) → (P x))))) 
  inductionCl psing popcl p1cl (sing x1) = (psing x1)  
  inductionCl psing popcl p1cl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl p1cl x1) (inductionCl psing popcl p1cl x2))  
  inductionCl psing popcl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpCommutativeMonoid1OLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativeMonoid1OLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P 1OL) → ( (x : (OpCommutativeMonoid1OLTerm n)) → (P x))))) 
  inductionOpB pv popol p1ol (v x1) = (pv x1)  
  inductionOpB pv popol p1ol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol p1ol x1) (inductionOpB pv popol p1ol x2))  
  inductionOpB pv popol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpCommutativeMonoid1OL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativeMonoid1OL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P 1OL2) → ( (x : (OpCommutativeMonoid1OL2Term2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 popol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 p1ol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 p1ol2 x1) (inductionOp pv2 psing2 popol2 p1ol2 x2))  
  inductionOp pv2 psing2 popol2 p1ol2 1OL2 = p1ol2  
  stageB :  (CommutativeMonoid1LTerm → (Staged CommutativeMonoid1LTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClCommutativeMonoid1ClTerm A) → (Staged (ClCommutativeMonoid1ClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpCommutativeMonoid1OLTerm n) → (Staged (OpCommutativeMonoid1OLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpCommutativeMonoid1OL2Term2 n A) → (Staged (OpCommutativeMonoid1OL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A)  
  
 