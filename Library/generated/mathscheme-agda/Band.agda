
module Band   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Band  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      idempotent_op : ( {x : A} → (op x x) ≡ x)  
  
  open Band
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      idempotent_opP : ( {xP : (Prod A A)} → (opP xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ba1 : (Band A1)) (Ba2 : (Band A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ba1) x1 x2)) ≡ ((op Ba2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ba1 : (Band A1)) (Ba2 : (Band A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ba1) x1 x2) ((op Ba2) y1 y2)))))  
  
  data BandTerm   : Set where 
      opL : (BandTerm → (BandTerm → BandTerm))  
      
  data ClBandTerm  (A : Set) : Set where 
      sing : (A → (ClBandTerm A)) 
      opCl : ((ClBandTerm A) → ((ClBandTerm A) → (ClBandTerm A)))  
      
  data OpBandTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBandTerm n)) 
      opOL : ((OpBandTerm n) → ((OpBandTerm n) → (OpBandTerm n)))  
      
  data OpBandTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBandTerm2 n A)) 
      sing2 : (A → (OpBandTerm2 n A)) 
      opOL2 : ((OpBandTerm2 n A) → ((OpBandTerm2 n A) → (OpBandTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClBandTerm A) → (ClBandTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpBandTerm n) → (OpBandTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpBandTerm2 n A) → (OpBandTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Band A) → (BandTerm → A)) 
  evalB Ba (opL x1 x2) = ((op Ba) (evalB Ba x1) (evalB Ba x2))  
  evalCl :  {A : Set} →  ((Band A) → ((ClBandTerm A) → A)) 
  evalCl Ba (sing x1) = x1  
  evalCl Ba (opCl x1 x2) = ((op Ba) (evalCl Ba x1) (evalCl Ba x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Band A) → ((Vec A n) → ((OpBandTerm n) → A))) 
  evalOpB n Ba vars (v x1) = (lookup vars x1)  
  evalOpB n Ba vars (opOL x1 x2) = ((op Ba) (evalOpB n Ba vars x1) (evalOpB n Ba vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Band A) → ((Vec A n) → ((OpBandTerm2 n A) → A))) 
  evalOp n Ba vars (v2 x1) = (lookup vars x1)  
  evalOp n Ba vars (sing2 x1) = x1  
  evalOp n Ba vars (opOL2 x1 x2) = ((op Ba) (evalOp n Ba vars x1) (evalOp n Ba vars x2))  
  inductionB :  (P : (BandTerm → Set)) →  (( (x1 x2 : BandTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : BandTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClBandTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBandTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClBandTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpBandTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBandTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpBandTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpBandTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBandTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpBandTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (BandTerm → (Staged BandTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClBandTerm A) → (Staged (ClBandTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpBandTerm n) → (Staged (OpBandTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpBandTerm2 n A) → (Staged (OpBandTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 