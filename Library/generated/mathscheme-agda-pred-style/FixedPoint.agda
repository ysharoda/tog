
module FixedPoint   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsFixedPoint  (A : Set) (prim : (A → A)) (e : A) : Set where 
     field  
      fixes_prim_e : (prim e) ≡ e  
  
  record FixedPoint  (A : Set) : Set where 
     field  
      prim : (A → A) 
      e : A 
      isFixedPoint : (IsFixedPoint A prim e)  
  
  open FixedPoint
  record Sig  (AS : Set) : Set where 
     field  
      primS : (AS → AS) 
      eS : AS  
  
  record Product  (A : Set) : Set where 
     field  
      primP : ((Prod A A) → (Prod A A)) 
      eP : (Prod A A) 
      fixes_prim_eP : (primP eP) ≡ eP  
  
  record Hom  {A1 : Set} {A2 : Set} (Fi1 : (FixedPoint A1)) (Fi2 : (FixedPoint A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-prim : ( {x1 : A1} → (hom ((prim Fi1) x1)) ≡ ((prim Fi2) (hom x1))) 
      pres-e : (hom (e Fi1)) ≡ (e Fi2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Fi1 : (FixedPoint A1)) (Fi2 : (FixedPoint A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Fi1) x1) ((prim Fi2) y1)))) 
      interp-e : (interp (e Fi1) (e Fi2))  
  
  data FixedPointTerm   : Set where 
      primL : (FixedPointTerm → FixedPointTerm) 
      eL : FixedPointTerm  
      
  data ClFixedPointTerm  (A : Set) : Set where 
      sing : (A → (ClFixedPointTerm A)) 
      primCl : ((ClFixedPointTerm A) → (ClFixedPointTerm A)) 
      eCl : (ClFixedPointTerm A)  
      
  data OpFixedPointTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpFixedPointTerm n)) 
      primOL : ((OpFixedPointTerm n) → (OpFixedPointTerm n)) 
      eOL : (OpFixedPointTerm n)  
      
  data OpFixedPointTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpFixedPointTerm2 n A)) 
      sing2 : (A → (OpFixedPointTerm2 n A)) 
      primOL2 : ((OpFixedPointTerm2 n A) → (OpFixedPointTerm2 n A)) 
      eOL2 : (OpFixedPointTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClFixedPointTerm A) → (ClFixedPointTerm A)) 
  simplifyCl (primCl eCl) = eCl  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl eCl = eCl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpFixedPointTerm n) → (OpFixedPointTerm n)) 
  simplifyOpB (primOL eOL) = eOL  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB eOL = eOL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpFixedPointTerm2 n A) → (OpFixedPointTerm2 n A)) 
  simplifyOp (primOL2 eOL2) = eOL2  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((FixedPoint A) → (FixedPointTerm → A)) 
  evalB Fi (primL x1) = ((prim Fi) (evalB Fi x1))  
  evalB Fi eL = (e Fi)  
  evalCl :  {A : Set} →  ((FixedPoint A) → ((ClFixedPointTerm A) → A)) 
  evalCl Fi (sing x1) = x1  
  evalCl Fi (primCl x1) = ((prim Fi) (evalCl Fi x1))  
  evalCl Fi eCl = (e Fi)  
  evalOpB :  {A : Set} {n : Nat} →  ((FixedPoint A) → ((Vec A n) → ((OpFixedPointTerm n) → A))) 
  evalOpB Fi vars (v x1) = (lookup vars x1)  
  evalOpB Fi vars (primOL x1) = ((prim Fi) (evalOpB Fi vars x1))  
  evalOpB Fi vars eOL = (e Fi)  
  evalOp :  {A : Set} {n : Nat} →  ((FixedPoint A) → ((Vec A n) → ((OpFixedPointTerm2 n A) → A))) 
  evalOp Fi vars (v2 x1) = (lookup vars x1)  
  evalOp Fi vars (sing2 x1) = x1  
  evalOp Fi vars (primOL2 x1) = ((prim Fi) (evalOp Fi vars x1))  
  evalOp Fi vars eOL2 = (e Fi)  
  inductionB :  {P : (FixedPointTerm → Set)} →  (( (x1 : FixedPointTerm) → ((P x1) → (P (primL x1)))) → ((P eL) → ( (x : FixedPointTerm) → (P x)))) 
  inductionB ppriml pel (primL x1) = (ppriml _ (inductionB ppriml pel x1))  
  inductionB ppriml pel eL = pel  
  inductionCl :  {A : Set} {P : ((ClFixedPointTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClFixedPointTerm A)) → ((P x1) → (P (primCl x1)))) → ((P eCl) → ( (x : (ClFixedPointTerm A)) → (P x))))) 
  inductionCl psing pprimcl pecl (sing x1) = (psing x1)  
  inductionCl psing pprimcl pecl (primCl x1) = (pprimcl _ (inductionCl psing pprimcl pecl x1))  
  inductionCl psing pprimcl pecl eCl = pecl  
  inductionOpB :  {n : Nat} {P : ((OpFixedPointTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpFixedPointTerm n)) → ((P x1) → (P (primOL x1)))) → ((P eOL) → ( (x : (OpFixedPointTerm n)) → (P x))))) 
  inductionOpB pv pprimol peol (v x1) = (pv x1)  
  inductionOpB pv pprimol peol (primOL x1) = (pprimol _ (inductionOpB pv pprimol peol x1))  
  inductionOpB pv pprimol peol eOL = peol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpFixedPointTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpFixedPointTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ((P eOL2) → ( (x : (OpFixedPointTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 pprimol2 peol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 pprimol2 peol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 pprimol2 peol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 pprimol2 peol2 x1))  
  inductionOp pv2 psing2 pprimol2 peol2 eOL2 = peol2  
  stageB :  (FixedPointTerm → (Staged FixedPointTerm))
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB eL = (Now eL)  
  stageCl :  {A : Set} →  ((ClFixedPointTerm A) → (Staged (ClFixedPointTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl eCl = (Now eCl)  
  stageOpB :  {n : Nat} →  ((OpFixedPointTerm n) → (Staged (OpFixedPointTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB eOL = (Now eOL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpFixedPointTerm2 n A) → (Staged (OpFixedPointTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp eOL2 = (Now eOL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      primT : ((Repr A) → (Repr A)) 
      eT : (Repr A)  
  
 