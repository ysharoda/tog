
module SteinerMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsSteinerMagma  (A : Set) (op : (A → (A → A))) : Set where 
     field  
      commutative_op : ( {x y : A} → (op x y) ≡ (op y x)) 
      antiAbsorbent : ( {x y : A} → (op x (op x y)) ≡ y)  
  
  record SteinerMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      isSteinerMagma : (IsSteinerMagma A op)  
  
  open SteinerMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_opP : ( {xP yP : (Prod A A)} → (opP xP yP) ≡ (opP yP xP)) 
      antiAbsorbentP : ( {xP yP : (Prod A A)} → (opP xP (opP xP yP)) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (St1 : (SteinerMagma A1)) (St2 : (SteinerMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op St1) x1 x2)) ≡ ((op St2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (St1 : (SteinerMagma A1)) (St2 : (SteinerMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op St1) x1 x2) ((op St2) y1 y2)))))  
  
  data SteinerMagmaTerm   : Set where 
      opL : (SteinerMagmaTerm → (SteinerMagmaTerm → SteinerMagmaTerm))  
      
  data ClSteinerMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClSteinerMagmaTerm A)) 
      opCl : ((ClSteinerMagmaTerm A) → ((ClSteinerMagmaTerm A) → (ClSteinerMagmaTerm A)))  
      
  data OpSteinerMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpSteinerMagmaTerm n)) 
      opOL : ((OpSteinerMagmaTerm n) → ((OpSteinerMagmaTerm n) → (OpSteinerMagmaTerm n)))  
      
  data OpSteinerMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpSteinerMagmaTerm2 n A)) 
      sing2 : (A → (OpSteinerMagmaTerm2 n A)) 
      opOL2 : ((OpSteinerMagmaTerm2 n A) → ((OpSteinerMagmaTerm2 n A) → (OpSteinerMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClSteinerMagmaTerm A) → (ClSteinerMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpSteinerMagmaTerm n) → (OpSteinerMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpSteinerMagmaTerm2 n A) → (OpSteinerMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((SteinerMagma A) → (SteinerMagmaTerm → A)) 
  evalB St (opL x1 x2) = ((op St) (evalB St x1) (evalB St x2))  
  evalCl :  {A : Set} →  ((SteinerMagma A) → ((ClSteinerMagmaTerm A) → A)) 
  evalCl St (sing x1) = x1  
  evalCl St (opCl x1 x2) = ((op St) (evalCl St x1) (evalCl St x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((SteinerMagma A) → ((Vec A n) → ((OpSteinerMagmaTerm n) → A))) 
  evalOpB n St vars (v x1) = (lookup vars x1)  
  evalOpB n St vars (opOL x1 x2) = ((op St) (evalOpB n St vars x1) (evalOpB n St vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((SteinerMagma A) → ((Vec A n) → ((OpSteinerMagmaTerm2 n A) → A))) 
  evalOp n St vars (v2 x1) = (lookup vars x1)  
  evalOp n St vars (sing2 x1) = x1  
  evalOp n St vars (opOL2 x1 x2) = ((op St) (evalOp n St vars x1) (evalOp n St vars x2))  
  inductionB :  (P : (SteinerMagmaTerm → Set)) →  (( (x1 x2 : SteinerMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : SteinerMagmaTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClSteinerMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClSteinerMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClSteinerMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpSteinerMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpSteinerMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpSteinerMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpSteinerMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpSteinerMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpSteinerMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (SteinerMagmaTerm → (Staged SteinerMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClSteinerMagmaTerm A) → (Staged (ClSteinerMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpSteinerMagmaTerm n) → (Staged (OpSteinerMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpSteinerMagmaTerm2 n A) → (Staged (OpSteinerMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 