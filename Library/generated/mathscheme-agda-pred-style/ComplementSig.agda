
module ComplementSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsComplementSig  (A : Set) (compl : (A → A)) : Set where 
    
  record ComplementSig  (A : Set) : Set where 
     field  
      compl : (A → A) 
      isComplementSig : (IsComplementSig A compl)  
  
  open ComplementSig
  record Sig  (AS : Set) : Set where 
     field  
      complS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      complP : ((Prod A A) → (Prod A A))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (ComplementSig A1)) (Co2 : (ComplementSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-compl : ( {x1 : A1} → (hom ((compl Co1) x1)) ≡ ((compl Co2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (ComplementSig A1)) (Co2 : (ComplementSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-compl : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((compl Co1) x1) ((compl Co2) y1))))  
  
  data ComplementSigTerm   : Set where 
      complL : (ComplementSigTerm → ComplementSigTerm)  
      
  data ClComplementSigTerm  (A : Set) : Set where 
      sing : (A → (ClComplementSigTerm A)) 
      complCl : ((ClComplementSigTerm A) → (ClComplementSigTerm A))  
      
  data OpComplementSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpComplementSigTerm n)) 
      complOL : ((OpComplementSigTerm n) → (OpComplementSigTerm n))  
      
  data OpComplementSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpComplementSigTerm2 n A)) 
      sing2 : (A → (OpComplementSigTerm2 n A)) 
      complOL2 : ((OpComplementSigTerm2 n A) → (OpComplementSigTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClComplementSigTerm A) → (ClComplementSigTerm A)) 
  simplifyCl _ (complCl x1) = (complCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpComplementSigTerm n) → (OpComplementSigTerm n)) 
  simplifyOpB _ (complOL x1) = (complOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpComplementSigTerm2 n A) → (OpComplementSigTerm2 n A)) 
  simplifyOp _ _ (complOL2 x1) = (complOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((ComplementSig A) → (ComplementSigTerm → A)) 
  evalB Co (complL x1) = ((compl Co) (evalB Co x1))  
  evalCl :  {A : Set} →  ((ComplementSig A) → ((ClComplementSigTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (complCl x1) = ((compl Co) (evalCl Co x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((ComplementSig A) → ((Vec A n) → ((OpComplementSigTerm n) → A))) 
  evalOpB n Co vars (v x1) = (lookup vars x1)  
  evalOpB n Co vars (complOL x1) = ((compl Co) (evalOpB n Co vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((ComplementSig A) → ((Vec A n) → ((OpComplementSigTerm2 n A) → A))) 
  evalOp n Co vars (v2 x1) = (lookup vars x1)  
  evalOp n Co vars (sing2 x1) = x1  
  evalOp n Co vars (complOL2 x1) = ((compl Co) (evalOp n Co vars x1))  
  inductionB :  (P : (ComplementSigTerm → Set)) →  (( (x1 : ComplementSigTerm) → ((P x1) → (P (complL x1)))) → ( (x : ComplementSigTerm) → (P x))) 
  inductionB p pcompll (complL x1) = (pcompll _ (inductionB p pcompll x1))  
  inductionCl :  (A : Set) (P : ((ClComplementSigTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 : (ClComplementSigTerm A)) → ((P x1) → (P (complCl x1)))) → ( (x : (ClComplementSigTerm A)) → (P x)))) 
  inductionCl _ p psing pcomplcl (sing x1) = (psing x1)  
  inductionCl _ p psing pcomplcl (complCl x1) = (pcomplcl _ (inductionCl _ p psing pcomplcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpComplementSigTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 : (OpComplementSigTerm n)) → ((P x1) → (P (complOL x1)))) → ( (x : (OpComplementSigTerm n)) → (P x)))) 
  inductionOpB _ p pv pcomplol (v x1) = (pv x1)  
  inductionOpB _ p pv pcomplol (complOL x1) = (pcomplol _ (inductionOpB _ p pv pcomplol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpComplementSigTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 : (OpComplementSigTerm2 n A)) → ((P x1) → (P (complOL2 x1)))) → ( (x : (OpComplementSigTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 pcomplol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 pcomplol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 pcomplol2 (complOL2 x1) = (pcomplol2 _ (inductionOp _ _ p pv2 psing2 pcomplol2 x1))  
  stageB :  (ComplementSigTerm → (Staged ComplementSigTerm))
  stageB (complL x1) = (stage1 complL (codeLift1 complL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClComplementSigTerm A) → (Staged (ClComplementSigTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (complCl x1) = (stage1 complCl (codeLift1 complCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpComplementSigTerm n) → (Staged (OpComplementSigTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (complOL x1) = (stage1 complOL (codeLift1 complOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpComplementSigTerm2 n A) → (Staged (OpComplementSigTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (complOL2 x1) = (stage1 complOL2 (codeLift1 complOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      complT : ((Repr A) → (Repr A))  
  
 