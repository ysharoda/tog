
module LeftUnital   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftUnital  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      lunit_e : ( {x : A} → (op e x) ≡ x)  
  
  open LeftUnital
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftUnital A1)) (Le2 : (LeftUnital A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Le1)) ≡ (e Le2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftUnital A1)) (Le2 : (LeftUnital A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Le1) (e Le2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))  
  
  data LeftUnitalTerm   : Set where 
      eL : LeftUnitalTerm 
      opL : (LeftUnitalTerm → (LeftUnitalTerm → LeftUnitalTerm))  
      
  data ClLeftUnitalTerm  (A : Set) : Set where 
      sing : (A → (ClLeftUnitalTerm A)) 
      eCl : (ClLeftUnitalTerm A) 
      opCl : ((ClLeftUnitalTerm A) → ((ClLeftUnitalTerm A) → (ClLeftUnitalTerm A)))  
      
  data OpLeftUnitalTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftUnitalTerm n)) 
      eOL : (OpLeftUnitalTerm n) 
      opOL : ((OpLeftUnitalTerm n) → ((OpLeftUnitalTerm n) → (OpLeftUnitalTerm n)))  
      
  data OpLeftUnitalTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftUnitalTerm2 n A)) 
      sing2 : (A → (OpLeftUnitalTerm2 n A)) 
      eOL2 : (OpLeftUnitalTerm2 n A) 
      opOL2 : ((OpLeftUnitalTerm2 n A) → ((OpLeftUnitalTerm2 n A) → (OpLeftUnitalTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClLeftUnitalTerm A) → (ClLeftUnitalTerm A)) 
  simplifyCl _ (opCl eCl x) = x  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpLeftUnitalTerm n) → (OpLeftUnitalTerm n)) 
  simplifyOpB _ (opOL eOL x) = x  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpLeftUnitalTerm2 n A) → (OpLeftUnitalTerm2 n A)) 
  simplifyOp _ _ (opOL2 eOL2 x) = x  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftUnital A) → (LeftUnitalTerm → A)) 
  evalB Le eL = (e Le)  
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftUnital A) → ((ClLeftUnitalTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le eCl = (e Le)  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((LeftUnital A) → ((Vec A n) → ((OpLeftUnitalTerm n) → A))) 
  evalOpB n Le vars (v x1) = (lookup vars x1)  
  evalOpB n Le vars eOL = (e Le)  
  evalOpB n Le vars (opOL x1 x2) = ((op Le) (evalOpB n Le vars x1) (evalOpB n Le vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((LeftUnital A) → ((Vec A n) → ((OpLeftUnitalTerm2 n A) → A))) 
  evalOp n Le vars (v2 x1) = (lookup vars x1)  
  evalOp n Le vars (sing2 x1) = x1  
  evalOp n Le vars eOL2 = (e Le)  
  evalOp n Le vars (opOL2 x1 x2) = ((op Le) (evalOp n Le vars x1) (evalOp n Le vars x2))  
  inductionB :  (P : (LeftUnitalTerm → Set)) →  ((P eL) → (( (x1 x2 : LeftUnitalTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : LeftUnitalTerm) → (P x)))) 
  inductionB p pel popl eL = pel  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))  
  inductionCl :  (A : Set) (P : ((ClLeftUnitalTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClLeftUnitalTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClLeftUnitalTerm A)) → (P x))))) 
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pecl popcl eCl = pecl  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpLeftUnitalTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpLeftUnitalTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpLeftUnitalTerm n)) → (P x))))) 
  inductionOpB _ p pv peol popol (v x1) = (pv x1)  
  inductionOpB _ p pv peol popol eOL = peol  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpLeftUnitalTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpLeftUnitalTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpLeftUnitalTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))  
  stageB :  (LeftUnitalTerm → (Staged LeftUnitalTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClLeftUnitalTerm A) → (Staged (ClLeftUnitalTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpLeftUnitalTerm n) → (Staged (OpLeftUnitalTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpLeftUnitalTerm2 n A) → (Staged (OpLeftUnitalTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 