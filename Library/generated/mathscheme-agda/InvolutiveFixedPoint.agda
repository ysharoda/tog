
module InvolutiveFixedPoint   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveFixedPoint  (A : Set) : Set where 
     field  
      prim : (A → A) 
      1ᵢ : A 
      fixes_prim_1ᵢ : (prim 1ᵢ) ≡ 1ᵢ 
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x)  
  
  open InvolutiveFixedPoint
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      1P : (Prod A A) 
      fixes_prim_1P : (primP 1P) ≡ 1P 
      involutive_primP : ( {xP : (Prod A A)} → (primP (primP xP)) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveFixedPoint A1)) (In2 : (InvolutiveFixedPoint A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1))) 
      pres-1 : (hom (1ᵢ In1)) ≡ (1ᵢ In2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveFixedPoint A1)) (In2 : (InvolutiveFixedPoint A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))) 
      interp-1 : (interp (1ᵢ In1) (1ᵢ In2))  
  
  data InvolutiveFixedPointTerm   : Set where 
      primL : (InvolutiveFixedPointTerm → InvolutiveFixedPointTerm) 
      1L : InvolutiveFixedPointTerm  
      
  data ClInvolutiveFixedPointTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveFixedPointTerm A)) 
      primCl : ((ClInvolutiveFixedPointTerm A) → (ClInvolutiveFixedPointTerm A)) 
      1Cl : (ClInvolutiveFixedPointTerm A)  
      
  data OpInvolutiveFixedPointTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveFixedPointTerm n)) 
      primOL : ((OpInvolutiveFixedPointTerm n) → (OpInvolutiveFixedPointTerm n)) 
      1OL : (OpInvolutiveFixedPointTerm n)  
      
  data OpInvolutiveFixedPointTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveFixedPointTerm2 n A)) 
      sing2 : (A → (OpInvolutiveFixedPointTerm2 n A)) 
      primOL2 : ((OpInvolutiveFixedPointTerm2 n A) → (OpInvolutiveFixedPointTerm2 n A)) 
      1OL2 : (OpInvolutiveFixedPointTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveFixedPointTerm A) → (ClInvolutiveFixedPointTerm A)) 
  simplifyCl (primCl 1Cl) = 1Cl  
  simplifyCl (primCl (primCl x)) = x  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveFixedPointTerm n) → (OpInvolutiveFixedPointTerm n)) 
  simplifyOpB (primOL 1OL) = 1OL  
  simplifyOpB (primOL (primOL x)) = x  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveFixedPointTerm2 n A) → (OpInvolutiveFixedPointTerm2 n A)) 
  simplifyOp (primOL2 1OL2) = 1OL2  
  simplifyOp (primOL2 (primOL2 x)) = x  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveFixedPoint A) → (InvolutiveFixedPointTerm → A)) 
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalB In 1L = (1ᵢ In)  
  evalCl :  {A : Set} →  ((InvolutiveFixedPoint A) → ((ClInvolutiveFixedPointTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalCl In 1Cl = (1ᵢ In)  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveFixedPoint A) → ((Vec A n) → ((OpInvolutiveFixedPointTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOpB In vars 1OL = (1ᵢ In)  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveFixedPoint A) → ((Vec A n) → ((OpInvolutiveFixedPointTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  evalOp In vars 1OL2 = (1ᵢ In)  
  inductionB :  {P : (InvolutiveFixedPointTerm → Set)} →  (( (x1 : InvolutiveFixedPointTerm) → ((P x1) → (P (primL x1)))) → ((P 1L) → ( (x : InvolutiveFixedPointTerm) → (P x)))) 
  inductionB ppriml p1l (primL x1) = (ppriml _ (inductionB ppriml p1l x1))  
  inductionB ppriml p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClInvolutiveFixedPointTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClInvolutiveFixedPointTerm A)) → ((P x1) → (P (primCl x1)))) → ((P 1Cl) → ( (x : (ClInvolutiveFixedPointTerm A)) → (P x))))) 
  inductionCl psing pprimcl p1cl (sing x1) = (psing x1)  
  inductionCl psing pprimcl p1cl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl p1cl x1))  
  inductionCl psing pprimcl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveFixedPointTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpInvolutiveFixedPointTerm n)) → ((P x1) → (P (primOL x1)))) → ((P 1OL) → ( (x : (OpInvolutiveFixedPointTerm n)) → (P x))))) 
  inductionOpB pv pprimol p1ol (v x1) = (pv x1)  
  inductionOpB pv pprimol p1ol (primOL x1) = (pprimol _ (inductionOpB pv pprimol p1ol x1))  
  inductionOpB pv pprimol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveFixedPointTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpInvolutiveFixedPointTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ((P 1OL2) → ( (x : (OpInvolutiveFixedPointTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 pprimol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 p1ol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 p1ol2 x1))  
  inductionOp pv2 psing2 pprimol2 p1ol2 1OL2 = p1ol2  
  stageB :  (InvolutiveFixedPointTerm → (Staged InvolutiveFixedPointTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClInvolutiveFixedPointTerm A) → (Staged (ClInvolutiveFixedPointTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpInvolutiveFixedPointTerm n) → (Staged (OpInvolutiveFixedPointTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveFixedPointTerm2 n A) → (Staged (OpInvolutiveFixedPointTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      1T : (Repr A)  
  
 