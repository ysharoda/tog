
module NormalBand   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsNormalBand  (A : Set) (op : (A → (A → A))) : Set where 
     field  
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      idempotent_op : ( {x : A} → (op x x) ≡ x) 
      middleCommute_* : ( {x y z : A} → (op (op (op x y) z) x) ≡ (op (op (op x z) y) x))  
  
  record NormalBand  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      isNormalBand : (IsNormalBand A op)  
  
  open NormalBand
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      idempotent_opP : ( {xP : (Prod A A)} → (opP xP xP) ≡ xP) 
      middleCommute_*P : ( {xP yP zP : (Prod A A)} → (opP (opP (opP xP yP) zP) xP) ≡ (opP (opP (opP xP zP) yP) xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (No1 : (NormalBand A1)) (No2 : (NormalBand A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op No1) x1 x2)) ≡ ((op No2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (No1 : (NormalBand A1)) (No2 : (NormalBand A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op No1) x1 x2) ((op No2) y1 y2)))))  
  
  data NormalBandTerm   : Set where 
      opL : (NormalBandTerm → (NormalBandTerm → NormalBandTerm))  
      
  data ClNormalBandTerm  (A : Set) : Set where 
      sing : (A → (ClNormalBandTerm A)) 
      opCl : ((ClNormalBandTerm A) → ((ClNormalBandTerm A) → (ClNormalBandTerm A)))  
      
  data OpNormalBandTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpNormalBandTerm n)) 
      opOL : ((OpNormalBandTerm n) → ((OpNormalBandTerm n) → (OpNormalBandTerm n)))  
      
  data OpNormalBandTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpNormalBandTerm2 n A)) 
      sing2 : (A → (OpNormalBandTerm2 n A)) 
      opOL2 : ((OpNormalBandTerm2 n A) → ((OpNormalBandTerm2 n A) → (OpNormalBandTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClNormalBandTerm A) → (ClNormalBandTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpNormalBandTerm n) → (OpNormalBandTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpNormalBandTerm2 n A) → (OpNormalBandTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((NormalBand A) → (NormalBandTerm → A)) 
  evalB No (opL x1 x2) = ((op No) (evalB No x1) (evalB No x2))  
  evalCl :  {A : Set} →  ((NormalBand A) → ((ClNormalBandTerm A) → A)) 
  evalCl No (sing x1) = x1  
  evalCl No (opCl x1 x2) = ((op No) (evalCl No x1) (evalCl No x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((NormalBand A) → ((Vec A n) → ((OpNormalBandTerm n) → A))) 
  evalOpB No vars (v x1) = (lookup vars x1)  
  evalOpB No vars (opOL x1 x2) = ((op No) (evalOpB No vars x1) (evalOpB No vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((NormalBand A) → ((Vec A n) → ((OpNormalBandTerm2 n A) → A))) 
  evalOp No vars (v2 x1) = (lookup vars x1)  
  evalOp No vars (sing2 x1) = x1  
  evalOp No vars (opOL2 x1 x2) = ((op No) (evalOp No vars x1) (evalOp No vars x2))  
  inductionB :  {P : (NormalBandTerm → Set)} →  (( (x1 x2 : NormalBandTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : NormalBandTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClNormalBandTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClNormalBandTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClNormalBandTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpNormalBandTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpNormalBandTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpNormalBandTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpNormalBandTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpNormalBandTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpNormalBandTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (NormalBandTerm → (Staged NormalBandTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClNormalBandTerm A) → (Staged (ClNormalBandTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpNormalBandTerm n) → (Staged (OpNormalBandTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpNormalBandTerm2 n A) → (Staged (OpNormalBandTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 