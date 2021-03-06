
module RectangularBand   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRectangularBand  (A : Set) (op : (A → (A → A))) : Set where 
     field  
      associative_op : ( {x y z : A} → (op (op x y) z) ≡ (op x (op y z))) 
      idempotent_op : ( {x : A} → (op x x) ≡ x) 
      middleCommute_* : ( {x y z : A} → (op (op (op x y) z) x) ≡ (op (op (op x z) y) x))  
  
  record RectangularBand  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      isRectangularBand : (IsRectangularBand A op)  
  
  open RectangularBand
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      associative_opP : ( {xP yP zP : (Prod A A)} → (opP (opP xP yP) zP) ≡ (opP xP (opP yP zP))) 
      idempotent_opP : ( {xP : (Prod A A)} → (opP xP xP) ≡ xP) 
      middleCommute_*P : ( {xP yP zP : (Prod A A)} → (opP (opP (opP xP yP) zP) xP) ≡ (opP (opP (opP xP zP) yP) xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Re1 : (RectangularBand A1)) (Re2 : (RectangularBand A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Re1) x1 x2)) ≡ ((op Re2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Re1 : (RectangularBand A1)) (Re2 : (RectangularBand A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Re1) x1 x2) ((op Re2) y1 y2)))))  
  
  data RectangularBandTerm   : Set where 
      opL : (RectangularBandTerm → (RectangularBandTerm → RectangularBandTerm))  
      
  data ClRectangularBandTerm  (A : Set) : Set where 
      sing : (A → (ClRectangularBandTerm A)) 
      opCl : ((ClRectangularBandTerm A) → ((ClRectangularBandTerm A) → (ClRectangularBandTerm A)))  
      
  data OpRectangularBandTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRectangularBandTerm n)) 
      opOL : ((OpRectangularBandTerm n) → ((OpRectangularBandTerm n) → (OpRectangularBandTerm n)))  
      
  data OpRectangularBandTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRectangularBandTerm2 n A)) 
      sing2 : (A → (OpRectangularBandTerm2 n A)) 
      opOL2 : ((OpRectangularBandTerm2 n A) → ((OpRectangularBandTerm2 n A) → (OpRectangularBandTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRectangularBandTerm A) → (ClRectangularBandTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRectangularBandTerm n) → (OpRectangularBandTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRectangularBandTerm2 n A) → (OpRectangularBandTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RectangularBand A) → (RectangularBandTerm → A)) 
  evalB Re (opL x1 x2) = ((op Re) (evalB Re x1) (evalB Re x2))  
  evalCl :  {A : Set} →  ((RectangularBand A) → ((ClRectangularBandTerm A) → A)) 
  evalCl Re (sing x1) = x1  
  evalCl Re (opCl x1 x2) = ((op Re) (evalCl Re x1) (evalCl Re x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RectangularBand A) → ((Vec A n) → ((OpRectangularBandTerm n) → A))) 
  evalOpB Re vars (v x1) = (lookup vars x1)  
  evalOpB Re vars (opOL x1 x2) = ((op Re) (evalOpB Re vars x1) (evalOpB Re vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RectangularBand A) → ((Vec A n) → ((OpRectangularBandTerm2 n A) → A))) 
  evalOp Re vars (v2 x1) = (lookup vars x1)  
  evalOp Re vars (sing2 x1) = x1  
  evalOp Re vars (opOL2 x1 x2) = ((op Re) (evalOp Re vars x1) (evalOp Re vars x2))  
  inductionB :  {P : (RectangularBandTerm → Set)} →  (( (x1 x2 : RectangularBandTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : RectangularBandTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClRectangularBandTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRectangularBandTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClRectangularBandTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRectangularBandTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRectangularBandTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpRectangularBandTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRectangularBandTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRectangularBandTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpRectangularBandTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (RectangularBandTerm → (Staged RectangularBandTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRectangularBandTerm A) → (Staged (ClRectangularBandTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRectangularBandTerm n) → (Staged (OpRectangularBandTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRectangularBandTerm2 n A) → (Staged (OpRectangularBandTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 