
module MedialMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MedialMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      mediates : ( {w x y z : A} → (op (op x y) (op z w)) ≡ (op (op x z) (op y w)))  
  
  open MedialMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      mediatesP : ( {wP xP yP zP : (Prod A A)} → (opP (opP xP yP) (opP zP wP)) ≡ (opP (opP xP zP) (opP yP wP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Me1 : (MedialMagma A1)) (Me2 : (MedialMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Me1) x1 x2)) ≡ ((op Me2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Me1 : (MedialMagma A1)) (Me2 : (MedialMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Me1) x1 x2) ((op Me2) y1 y2)))))  
  
  data MedialMagmaTerm   : Set where 
      opL : (MedialMagmaTerm → (MedialMagmaTerm → MedialMagmaTerm))  
      
  data ClMedialMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClMedialMagmaTerm A)) 
      opCl : ((ClMedialMagmaTerm A) → ((ClMedialMagmaTerm A) → (ClMedialMagmaTerm A)))  
      
  data OpMedialMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMedialMagmaTerm n)) 
      opOL : ((OpMedialMagmaTerm n) → ((OpMedialMagmaTerm n) → (OpMedialMagmaTerm n)))  
      
  data OpMedialMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMedialMagmaTerm2 n A)) 
      sing2 : (A → (OpMedialMagmaTerm2 n A)) 
      opOL2 : ((OpMedialMagmaTerm2 n A) → ((OpMedialMagmaTerm2 n A) → (OpMedialMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMedialMagmaTerm A) → (ClMedialMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMedialMagmaTerm n) → (OpMedialMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMedialMagmaTerm2 n A) → (OpMedialMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MedialMagma A) → (MedialMagmaTerm → A)) 
  evalB Me (opL x1 x2) = ((op Me) (evalB Me x1) (evalB Me x2))  
  evalCl :  {A : Set} →  ((MedialMagma A) → ((ClMedialMagmaTerm A) → A)) 
  evalCl Me (sing x1) = x1  
  evalCl Me (opCl x1 x2) = ((op Me) (evalCl Me x1) (evalCl Me x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MedialMagma A) → ((Vec A n) → ((OpMedialMagmaTerm n) → A))) 
  evalOpB n Me vars (v x1) = (lookup vars x1)  
  evalOpB n Me vars (opOL x1 x2) = ((op Me) (evalOpB n Me vars x1) (evalOpB n Me vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MedialMagma A) → ((Vec A n) → ((OpMedialMagmaTerm2 n A) → A))) 
  evalOp n Me vars (v2 x1) = (lookup vars x1)  
  evalOp n Me vars (sing2 x1) = x1  
  evalOp n Me vars (opOL2 x1 x2) = ((op Me) (evalOp n Me vars x1) (evalOp n Me vars x2))  
  inductionB :  (P : (MedialMagmaTerm → Set)) →  (( (x1 x2 : MedialMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : MedialMagmaTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClMedialMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMedialMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClMedialMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMedialMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMedialMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpMedialMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMedialMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMedialMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpMedialMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (MedialMagmaTerm → (Staged MedialMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMedialMagmaTerm A) → (Staged (ClMedialMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMedialMagmaTerm n) → (Staged (OpMedialMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMedialMagmaTerm2 n A) → (Staged (OpMedialMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 