
module InvolutiveFixes   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveFixes  (A : Set) : Set where 
     field  
      1ᵢ : A 
      prim : (A → A) 
      fixes_prim_1ᵢ : (prim 1ᵢ) ≡ 1ᵢ  
  
  open InvolutiveFixes
  record Sig  (AS : Set) : Set where 
     field  
      1S : AS 
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      1P : (Prod A A) 
      primP : ((Prod A A) → (Prod A A)) 
      fixes_prim_1P : (primP 1P) ≡ 1P  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveFixes A1)) (In2 : (InvolutiveFixes A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-1 : (hom (1ᵢ In1)) ≡ (1ᵢ In2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveFixes A1)) (In2 : (InvolutiveFixes A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-1 : (interp (1ᵢ In1) (1ᵢ In2)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))  
  
  data InvolutiveFixesTerm   : Set where 
      1L : InvolutiveFixesTerm 
      primL : (InvolutiveFixesTerm → InvolutiveFixesTerm)  
      
  data ClInvolutiveFixesTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveFixesTerm A)) 
      1Cl : (ClInvolutiveFixesTerm A) 
      primCl : ((ClInvolutiveFixesTerm A) → (ClInvolutiveFixesTerm A))  
      
  data OpInvolutiveFixesTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveFixesTerm n)) 
      1OL : (OpInvolutiveFixesTerm n) 
      primOL : ((OpInvolutiveFixesTerm n) → (OpInvolutiveFixesTerm n))  
      
  data OpInvolutiveFixesTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveFixesTerm2 n A)) 
      sing2 : (A → (OpInvolutiveFixesTerm2 n A)) 
      1OL2 : (OpInvolutiveFixesTerm2 n A) 
      primOL2 : ((OpInvolutiveFixesTerm2 n A) → (OpInvolutiveFixesTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveFixesTerm A) → (ClInvolutiveFixesTerm A)) 
  simplifyCl (primCl 1Cl) = 1Cl  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveFixesTerm n) → (OpInvolutiveFixesTerm n)) 
  simplifyOpB (primOL 1OL) = 1OL  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveFixesTerm2 n A) → (OpInvolutiveFixesTerm2 n A)) 
  simplifyOp (primOL2 1OL2) = 1OL2  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveFixes A) → (InvolutiveFixesTerm → A)) 
  evalB In 1L = (1ᵢ In)  
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InvolutiveFixes A) → ((ClInvolutiveFixesTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In 1Cl = (1ᵢ In)  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveFixes A) → ((Vec A n) → ((OpInvolutiveFixesTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars 1OL = (1ᵢ In)  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveFixes A) → ((Vec A n) → ((OpInvolutiveFixesTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars 1OL2 = (1ᵢ In)  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  inductionB :  {P : (InvolutiveFixesTerm → Set)} →  ((P 1L) → (( (x1 : InvolutiveFixesTerm) → ((P x1) → (P (primL x1)))) → ( (x : InvolutiveFixesTerm) → (P x)))) 
  inductionB p1l ppriml 1L = p1l  
  inductionB p1l ppriml (primL x1) = (ppriml _ (inductionB p1l ppriml x1))  
  inductionCl :  {A : Set} {P : ((ClInvolutiveFixesTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 1Cl) → (( (x1 : (ClInvolutiveFixesTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClInvolutiveFixesTerm A)) → (P x))))) 
  inductionCl psing p1cl pprimcl (sing x1) = (psing x1)  
  inductionCl psing p1cl pprimcl 1Cl = p1cl  
  inductionCl psing p1cl pprimcl (primCl x1) = (pprimcl _ (inductionCl psing p1cl pprimcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveFixesTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 1OL) → (( (x1 : (OpInvolutiveFixesTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpInvolutiveFixesTerm n)) → (P x))))) 
  inductionOpB pv p1ol pprimol (v x1) = (pv x1)  
  inductionOpB pv p1ol pprimol 1OL = p1ol  
  inductionOpB pv p1ol pprimol (primOL x1) = (pprimol _ (inductionOpB pv p1ol pprimol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveFixesTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 1OL2) → (( (x1 : (OpInvolutiveFixesTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpInvolutiveFixesTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p1ol2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p1ol2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p1ol2 pprimol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p1ol2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 p1ol2 pprimol2 x1))  
  stageB :  (InvolutiveFixesTerm → (Staged InvolutiveFixesTerm))
  stageB 1L = (Now 1L)  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClInvolutiveFixesTerm A) → (Staged (ClInvolutiveFixesTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpInvolutiveFixesTerm n) → (Staged (OpInvolutiveFixesTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveFixesTerm2 n A) → (Staged (OpInvolutiveFixesTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      1T : (Repr A) 
      primT : ((Repr A) → (Repr A))  
  
 