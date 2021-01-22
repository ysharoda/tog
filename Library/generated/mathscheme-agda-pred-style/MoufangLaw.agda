
module MoufangLaw   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMoufangLaw  (A : Set) (op : (A → (A → A))) : Set where 
     field  
      moufangLaw : ( {e x y z : A} → ((op y e) ≡ y → (op (op (op x y) z) x) ≡ (op x (op y (op (op e z) x)))))  
  
  record MoufangLaw  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      isMoufangLaw : (IsMoufangLaw A op)  
  
  open MoufangLaw
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      moufangLawP : ( {eP xP yP zP : (Prod A A)} → ((opP yP eP) ≡ yP → (opP (opP (opP xP yP) zP) xP) ≡ (opP xP (opP yP (opP (opP eP zP) xP)))))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (MoufangLaw A1)) (Mo2 : (MoufangLaw A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Mo1) x1 x2)) ≡ ((op Mo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (MoufangLaw A1)) (Mo2 : (MoufangLaw A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2)))))  
  
  data MoufangLawTerm   : Set where 
      opL : (MoufangLawTerm → (MoufangLawTerm → MoufangLawTerm))  
      
  data ClMoufangLawTerm  (A : Set) : Set where 
      sing : (A → (ClMoufangLawTerm A)) 
      opCl : ((ClMoufangLawTerm A) → ((ClMoufangLawTerm A) → (ClMoufangLawTerm A)))  
      
  data OpMoufangLawTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMoufangLawTerm n)) 
      opOL : ((OpMoufangLawTerm n) → ((OpMoufangLawTerm n) → (OpMoufangLawTerm n)))  
      
  data OpMoufangLawTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMoufangLawTerm2 n A)) 
      sing2 : (A → (OpMoufangLawTerm2 n A)) 
      opOL2 : ((OpMoufangLawTerm2 n A) → ((OpMoufangLawTerm2 n A) → (OpMoufangLawTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClMoufangLawTerm A) → (ClMoufangLawTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpMoufangLawTerm n) → (OpMoufangLawTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpMoufangLawTerm2 n A) → (OpMoufangLawTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MoufangLaw A) → (MoufangLawTerm → A)) 
  evalB Mo (opL x1 x2) = ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  evalCl :  {A : Set} →  ((MoufangLaw A) → ((ClMoufangLawTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (opCl x1 x2) = ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((MoufangLaw A) → ((Vec A n) → ((OpMoufangLawTerm n) → A))) 
  evalOpB Mo vars (v x1) = (lookup vars x1)  
  evalOpB Mo vars (opOL x1 x2) = ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((MoufangLaw A) → ((Vec A n) → ((OpMoufangLawTerm2 n A) → A))) 
  evalOp Mo vars (v2 x1) = (lookup vars x1)  
  evalOp Mo vars (sing2 x1) = x1  
  evalOp Mo vars (opOL2 x1 x2) = ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  inductionB :  {P : (MoufangLawTerm → Set)} →  (( (x1 x2 : MoufangLawTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : MoufangLawTerm) → (P x))) 
  inductionB popl (opL x1 x2) = (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  inductionCl :  {A : Set} {P : ((ClMoufangLawTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMoufangLawTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClMoufangLawTerm A)) → (P x)))) 
  inductionCl psing popcl (sing x1) = (psing x1)  
  inductionCl psing popcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpMoufangLawTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMoufangLawTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpMoufangLawTerm n)) → (P x)))) 
  inductionOpB pv popol (v x1) = (pv x1)  
  inductionOpB pv popol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpMoufangLawTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMoufangLawTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpMoufangLawTerm2 n A)) → (P x))))) 
  inductionOp pv2 psing2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  stageB :  (MoufangLawTerm → (Staged MoufangLawTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClMoufangLawTerm A) → (Staged (ClMoufangLawTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpMoufangLawTerm n) → (Staged (OpMoufangLawTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpMoufangLawTerm2 n A) → (Staged (OpMoufangLawTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 