
module Left0   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeft0  (A : Set) (0ᵢ : A) (op : (A → (A → A))) : Set where 
     field  
      leftZero_op_0ᵢ : ( {x : A} → (op 0ᵢ x) ≡ 0ᵢ)  
  
  record Left0  (A : Set) : Set where 
     field  
      0ᵢ : A 
      op : (A → (A → A)) 
      isLeft0 : (IsLeft0 A 0ᵢ op)  
  
  open Left0
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (opP 0P xP) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (Left0 A1)) (Le2 : (Left0 A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Le1)) ≡ (0ᵢ Le2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (Left0 A1)) (Le2 : (Left0 A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Le1) (0ᵢ Le2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))  
  
  data Left0LTerm   : Set where 
      0L : Left0LTerm 
      opL : (Left0LTerm → (Left0LTerm → Left0LTerm))  
      
  data ClLeft0ClTerm  (A : Set) : Set where 
      sing : (A → (ClLeft0ClTerm A)) 
      0Cl : (ClLeft0ClTerm A) 
      opCl : ((ClLeft0ClTerm A) → ((ClLeft0ClTerm A) → (ClLeft0ClTerm A)))  
      
  data OpLeft0OLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeft0OLTerm n)) 
      0OL : (OpLeft0OLTerm n) 
      opOL : ((OpLeft0OLTerm n) → ((OpLeft0OLTerm n) → (OpLeft0OLTerm n)))  
      
  data OpLeft0OL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeft0OL2Term2 n A)) 
      sing2 : (A → (OpLeft0OL2Term2 n A)) 
      0OL2 : (OpLeft0OL2Term2 n A) 
      opOL2 : ((OpLeft0OL2Term2 n A) → ((OpLeft0OL2Term2 n A) → (OpLeft0OL2Term2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLeft0ClTerm A) → (ClLeft0ClTerm A)) 
  simplifyCl 0Cl = 0Cl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLeft0OLTerm n) → (OpLeft0OLTerm n)) 
  simplifyOpB 0OL = 0OL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLeft0OL2Term2 n A) → (OpLeft0OL2Term2 n A)) 
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Left0 A) → (Left0LTerm → A)) 
  evalB Le 0L = (0ᵢ Le)  
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((Left0 A) → ((ClLeft0ClTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le 0Cl = (0ᵢ Le)  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Left0 A) → ((Vec A n) → ((OpLeft0OLTerm n) → A))) 
  evalOpB Le vars (v x1) = (lookup vars x1)  
  evalOpB Le vars 0OL = (0ᵢ Le)  
  evalOpB Le vars (opOL x1 x2) = ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Left0 A) → ((Vec A n) → ((OpLeft0OL2Term2 n A) → A))) 
  evalOp Le vars (v2 x1) = (lookup vars x1)  
  evalOp Le vars (sing2 x1) = x1  
  evalOp Le vars 0OL2 = (0ᵢ Le)  
  evalOp Le vars (opOL2 x1 x2) = ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  inductionB :  {P : (Left0LTerm → Set)} →  ((P 0L) → (( (x1 x2 : Left0LTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : Left0LTerm) → (P x)))) 
  inductionB p0l popl 0L = p0l  
  inductionB p0l popl (opL x1 x2) = (popl _ _ (inductionB p0l popl x1) (inductionB p0l popl x2))  
  inductionCl :  {A : Set} {P : ((ClLeft0ClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClLeft0ClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClLeft0ClTerm A)) → (P x))))) 
  inductionCl psing p0cl popcl (sing x1) = (psing x1)  
  inductionCl psing p0cl popcl 0Cl = p0cl  
  inductionCl psing p0cl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing p0cl popcl x1) (inductionCl psing p0cl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLeft0OLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpLeft0OLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpLeft0OLTerm n)) → (P x))))) 
  inductionOpB pv p0ol popol (v x1) = (pv x1)  
  inductionOpB pv p0ol popol 0OL = p0ol  
  inductionOpB pv p0ol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv p0ol popol x1) (inductionOpB pv p0ol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLeft0OL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpLeft0OL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpLeft0OL2Term2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p0ol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 popol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 p0ol2 popol2 x1) (inductionOp pv2 psing2 p0ol2 popol2 x2))  
  stageB :  (Left0LTerm → (Staged Left0LTerm))
  stageB 0L = (Now 0L)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLeft0ClTerm A) → (Staged (ClLeft0ClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLeft0OLTerm n) → (Staged (OpLeft0OLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLeft0OL2Term2 n A) → (Staged (OpLeft0OL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 