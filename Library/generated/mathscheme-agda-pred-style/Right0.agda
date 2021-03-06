
module Right0   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRight0  (A : Set) (0ᵢ : A) (op : (A → (A → A))) : Set where 
     field  
      rightZero_op_0ᵢ : ( {x : A} → (op x 0ᵢ) ≡ 0ᵢ)  
  
  record Right0  (A : Set) : Set where 
     field  
      0ᵢ : A 
      op : (A → (A → A)) 
      isRight0 : (IsRight0 A 0ᵢ op)  
  
  open Right0
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (opP xP 0P) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (Right0 A1)) (Ri2 : (Right0 A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Ri1)) ≡ (0ᵢ Ri2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ri1) x1 x2)) ≡ ((op Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (Right0 A1)) (Ri2 : (Right0 A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Ri1) (0ᵢ Ri2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))  
  
  data Right0LTerm   : Set where 
      0L : Right0LTerm 
      opL : (Right0LTerm → (Right0LTerm → Right0LTerm))  
      
  data ClRight0ClTerm  (A : Set) : Set where 
      sing : (A → (ClRight0ClTerm A)) 
      0Cl : (ClRight0ClTerm A) 
      opCl : ((ClRight0ClTerm A) → ((ClRight0ClTerm A) → (ClRight0ClTerm A)))  
      
  data OpRight0OLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRight0OLTerm n)) 
      0OL : (OpRight0OLTerm n) 
      opOL : ((OpRight0OLTerm n) → ((OpRight0OLTerm n) → (OpRight0OLTerm n)))  
      
  data OpRight0OL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRight0OL2Term2 n A)) 
      sing2 : (A → (OpRight0OL2Term2 n A)) 
      0OL2 : (OpRight0OL2Term2 n A) 
      opOL2 : ((OpRight0OL2Term2 n A) → ((OpRight0OL2Term2 n A) → (OpRight0OL2Term2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRight0ClTerm A) → (ClRight0ClTerm A)) 
  simplifyCl 0Cl = 0Cl  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRight0OLTerm n) → (OpRight0OLTerm n)) 
  simplifyOpB 0OL = 0OL  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRight0OL2Term2 n A) → (OpRight0OL2Term2 n A)) 
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Right0 A) → (Right0LTerm → A)) 
  evalB Ri 0L = (0ᵢ Ri)  
  evalB Ri (opL x1 x2) = ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((Right0 A) → ((ClRight0ClTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri 0Cl = (0ᵢ Ri)  
  evalCl Ri (opCl x1 x2) = ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Right0 A) → ((Vec A n) → ((OpRight0OLTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars 0OL = (0ᵢ Ri)  
  evalOpB Ri vars (opOL x1 x2) = ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Right0 A) → ((Vec A n) → ((OpRight0OL2Term2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars 0OL2 = (0ᵢ Ri)  
  evalOp Ri vars (opOL2 x1 x2) = ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (Right0LTerm → Set)} →  ((P 0L) → (( (x1 x2 : Right0LTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : Right0LTerm) → (P x)))) 
  inductionB p0l popl 0L = p0l  
  inductionB p0l popl (opL x1 x2) = (popl _ _ (inductionB p0l popl x1) (inductionB p0l popl x2))  
  inductionCl :  {A : Set} {P : ((ClRight0ClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClRight0ClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClRight0ClTerm A)) → (P x))))) 
  inductionCl psing p0cl popcl (sing x1) = (psing x1)  
  inductionCl psing p0cl popcl 0Cl = p0cl  
  inductionCl psing p0cl popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing p0cl popcl x1) (inductionCl psing p0cl popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRight0OLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpRight0OLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpRight0OLTerm n)) → (P x))))) 
  inductionOpB pv p0ol popol (v x1) = (pv x1)  
  inductionOpB pv p0ol popol 0OL = p0ol  
  inductionOpB pv p0ol popol (opOL x1 x2) = (popol _ _ (inductionOpB pv p0ol popol x1) (inductionOpB pv p0ol popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRight0OL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpRight0OL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpRight0OL2Term2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p0ol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 popol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 p0ol2 popol2 x1) (inductionOp pv2 psing2 p0ol2 popol2 x2))  
  stageB :  (Right0LTerm → (Staged Right0LTerm))
  stageB 0L = (Now 0L)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRight0ClTerm A) → (Staged (ClRight0ClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRight0OLTerm n) → (Staged (OpRight0OLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRight0OL2Term2 n A) → (Staged (OpRight0OL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 