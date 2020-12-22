
module CommutativeMonoid1   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeMonoid1  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (op 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (op x 1ᵢ) ≡ x) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x))  
  
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
      
  simplifyCl :  (A : Set) →  ((ClCommutativeMonoid1ClTerm A) → (ClCommutativeMonoid1ClTerm A)) 
  simplifyCl _ (opCl 1Cl x) = x  
  simplifyCl _ (opCl x 1Cl) = x  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ 1Cl = 1Cl  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpCommutativeMonoid1OLTerm n) → (OpCommutativeMonoid1OLTerm n)) 
  simplifyOpB _ (opOL 1OL x) = x  
  simplifyOpB _ (opOL x 1OL) = x  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ 1OL = 1OL  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpCommutativeMonoid1OL2Term2 n A) → (OpCommutativeMonoid1OL2Term2 n A)) 
  simplifyOp _ _ (opOL2 1OL2 x) = x  
  simplifyOp _ _ (opOL2 x 1OL2) = x  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ 1OL2 = 1OL2  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativeMonoid1 A) → (CommutativeMonoid1LTerm → A)) 
  evalB Co (opL x1 x2) = ((op Co) (evalB Co x1) (evalB Co x2))  
  evalB Co 1L = (1ᵢ Co)  
  evalCl :  {A : Set} →  ((CommutativeMonoid1 A) → ((ClCommutativeMonoid1ClTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (opCl x1 x2) = ((op Co) (evalCl Co x1) (evalCl Co x2))  
  evalCl Co 1Cl = (1ᵢ Co)  
  evalOpB :  {A : Set} (n : Nat) →  ((CommutativeMonoid1 A) → ((Vec A n) → ((OpCommutativeMonoid1OLTerm n) → A))) 
  evalOpB n Co vars (v x1) = (lookup vars x1)  
  evalOpB n Co vars (opOL x1 x2) = ((op Co) (evalOpB n Co vars x1) (evalOpB n Co vars x2))  
  evalOpB n Co vars 1OL = (1ᵢ Co)  
  evalOp :  {A : Set} (n : Nat) →  ((CommutativeMonoid1 A) → ((Vec A n) → ((OpCommutativeMonoid1OL2Term2 n A) → A))) 
  evalOp n Co vars (v2 x1) = (lookup vars x1)  
  evalOp n Co vars (sing2 x1) = x1  
  evalOp n Co vars (opOL2 x1 x2) = ((op Co) (evalOp n Co vars x1) (evalOp n Co vars x2))  
  evalOp n Co vars 1OL2 = (1ᵢ Co)  
  inductionB :  (P : (CommutativeMonoid1LTerm → Set)) →  (( (x1 x2 : CommutativeMonoid1LTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P 1L) → ( (x : CommutativeMonoid1LTerm) → (P x)))) 
  inductionB p popl p1l (opL x1 x2) = (popl _ _ (inductionB p popl p1l x1) (inductionB p popl p1l x2))  
  inductionB p popl p1l 1L = p1l  
  inductionCl :  (A : Set) (P : ((ClCommutativeMonoid1ClTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativeMonoid1ClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P 1Cl) → ( (x : (ClCommutativeMonoid1ClTerm A)) → (P x))))) 
  inductionCl _ p psing popcl p1cl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl p1cl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl p1cl x1) (inductionCl _ p psing popcl p1cl x2))  
  inductionCl _ p psing popcl p1cl 1Cl = p1cl  
  inductionOpB :  (n : Nat) (P : ((OpCommutativeMonoid1OLTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativeMonoid1OLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P 1OL) → ( (x : (OpCommutativeMonoid1OLTerm n)) → (P x))))) 
  inductionOpB _ p pv popol p1ol (v x1) = (pv x1)  
  inductionOpB _ p pv popol p1ol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol p1ol x1) (inductionOpB _ p pv popol p1ol x2))  
  inductionOpB _ p pv popol p1ol 1OL = p1ol  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpCommutativeMonoid1OL2Term2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativeMonoid1OL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P 1OL2) → ( (x : (OpCommutativeMonoid1OL2Term2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 popol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 p1ol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 p1ol2 x1) (inductionOp _ _ p pv2 psing2 popol2 p1ol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 p1ol2 1OL2 = p1ol2  
  stageB :  (CommutativeMonoid1LTerm → (Staged CommutativeMonoid1LTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageCl :  (A : Set) →  ((ClCommutativeMonoid1ClTerm A) → (Staged (ClCommutativeMonoid1ClTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ 1Cl = (Now 1Cl)  
  stageOpB :  (n : Nat) →  ((OpCommutativeMonoid1OLTerm n) → (Staged (OpCommutativeMonoid1OLTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ 1OL = (Now 1OL)  
  stageOp :  (n : Nat) (A : Set) →  ((OpCommutativeMonoid1OL2Term2 n A) → (Staged (OpCommutativeMonoid1OL2Term2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A)  
  
 