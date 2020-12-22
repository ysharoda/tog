
module MoufangIdentity   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MoufangIdentity  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      moufangId : ( {x y z : A} → (op (op z x) (op y z)) ≡ (op (op z (op x y)) z))  
  
  open MoufangIdentity
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      moufangIdP : ( {xP yP zP : (Prod A A)} → (opP (opP zP xP) (opP yP zP)) ≡ (opP (opP zP (opP xP yP)) zP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (MoufangIdentity A1)) (Mo2 : (MoufangIdentity A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Mo1) x1 x2)) ≡ ((op Mo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (MoufangIdentity A1)) (Mo2 : (MoufangIdentity A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2)))))  
  
  data MoufangIdentityTerm   : Set where 
      opL : (MoufangIdentityTerm → (MoufangIdentityTerm → MoufangIdentityTerm))  
      
  data ClMoufangIdentityTerm  (A : Set) : Set where 
      sing : (A → (ClMoufangIdentityTerm A)) 
      opCl : ((ClMoufangIdentityTerm A) → ((ClMoufangIdentityTerm A) → (ClMoufangIdentityTerm A)))  
      
  data OpMoufangIdentityTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMoufangIdentityTerm n)) 
      opOL : ((OpMoufangIdentityTerm n) → ((OpMoufangIdentityTerm n) → (OpMoufangIdentityTerm n)))  
      
  data OpMoufangIdentityTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMoufangIdentityTerm2 n A)) 
      sing2 : (A → (OpMoufangIdentityTerm2 n A)) 
      opOL2 : ((OpMoufangIdentityTerm2 n A) → ((OpMoufangIdentityTerm2 n A) → (OpMoufangIdentityTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMoufangIdentityTerm A) → (ClMoufangIdentityTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMoufangIdentityTerm n) → (OpMoufangIdentityTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMoufangIdentityTerm2 n A) → (OpMoufangIdentityTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MoufangIdentity A) → (MoufangIdentityTerm → A)) 
  evalB Mo (opL x1 x2) = ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  evalCl :  {A : Set} →  ((MoufangIdentity A) → ((ClMoufangIdentityTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (opCl x1 x2) = ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MoufangIdentity A) → ((Vec A n) → ((OpMoufangIdentityTerm n) → A))) 
  evalOpB n Mo vars (v x1) = (lookup vars x1)  
  evalOpB n Mo vars (opOL x1 x2) = ((op Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MoufangIdentity A) → ((Vec A n) → ((OpMoufangIdentityTerm2 n A) → A))) 
  evalOp n Mo vars (v2 x1) = (lookup vars x1)  
  evalOp n Mo vars (sing2 x1) = x1  
  evalOp n Mo vars (opOL2 x1 x2) = ((op Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  inductionB :  (P : (MoufangIdentityTerm → Set)) →  (( (x1 x2 : MoufangIdentityTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : MoufangIdentityTerm) → (P x))) 
  inductionB p popl (opL x1 x2) = (popl _ _ (inductionB p popl x1) (inductionB p popl x2))  
  inductionCl :  (A : Set) (P : ((ClMoufangIdentityTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMoufangIdentityTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClMoufangIdentityTerm A)) → (P x)))) 
  inductionCl _ p psing popcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl x1) (inductionCl _ p psing popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMoufangIdentityTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMoufangIdentityTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpMoufangIdentityTerm n)) → (P x)))) 
  inductionOpB _ p pv popol (v x1) = (pv x1)  
  inductionOpB _ p pv popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol x1) (inductionOpB _ p pv popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMoufangIdentityTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMoufangIdentityTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpMoufangIdentityTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 x1) (inductionOp _ _ p pv2 psing2 popol2 x2))  
  stageB :  (MoufangIdentityTerm → (Staged MoufangIdentityTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMoufangIdentityTerm A) → (Staged (ClMoufangIdentityTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMoufangIdentityTerm n) → (Staged (OpMoufangIdentityTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMoufangIdentityTerm2 n A) → (Staged (OpMoufangIdentityTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 