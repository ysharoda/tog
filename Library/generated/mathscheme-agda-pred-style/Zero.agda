
module Zero   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsZero  (A : Set) (e : A) (op : (A → (A → A))) : Set where 
     field  
      leftZero_op_e : ( {x : A} → (op e x) ≡ e) 
      rightZero_op_e : ( {x : A} → (op x e) ≡ e)  
  
  record Zero  (A : Set) : Set where 
     field  
      e : A 
      op : (A → (A → A)) 
      isZero : (IsZero A e op)  
  
  open Zero
  record Sig  (AS : Set) : Set where 
     field  
      eS : AS 
      opS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      eP : (Prod A A) 
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftZero_op_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ eP) 
      rightZero_op_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ eP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ze1 : (Zero A1)) (Ze2 : (Zero A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-e : (hom (e Ze1)) ≡ (e Ze2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Ze1) x1 x2)) ≡ ((op Ze2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ze1 : (Zero A1)) (Ze2 : (Zero A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-e : (interp (e Ze1) (e Ze2)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ze1) x1 x2) ((op Ze2) y1 y2)))))  
  
  data ZeroTerm   : Set where 
      eL : ZeroTerm 
      opL : (ZeroTerm → (ZeroTerm → ZeroTerm))  
      
  data ClZeroTerm  (A : Set) : Set where 
      sing : (A → (ClZeroTerm A)) 
      eCl : (ClZeroTerm A) 
      opCl : ((ClZeroTerm A) → ((ClZeroTerm A) → (ClZeroTerm A)))  
      
  data OpZeroTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpZeroTerm n)) 
      eOL : (OpZeroTerm n) 
      opOL : ((OpZeroTerm n) → ((OpZeroTerm n) → (OpZeroTerm n)))  
      
  data OpZeroTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpZeroTerm2 n A)) 
      sing2 : (A → (OpZeroTerm2 n A)) 
      eOL2 : (OpZeroTerm2 n A) 
      opOL2 : ((OpZeroTerm2 n A) → ((OpZeroTerm2 n A) → (OpZeroTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClZeroTerm A) → (ClZeroTerm A)) 
  simplifyCl _ eCl = eCl  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpZeroTerm n) → (OpZeroTerm n)) 
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpZeroTerm2 n A) → (OpZeroTerm2 n A)) 
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Zero A) → (ZeroTerm → A)) 
  evalB Ze eL = (e Ze)  
  evalB Ze (opL x1 x2) = ((op Ze) (evalB Ze x1) (evalB Ze x2))  
  evalCl :  {A : Set} →  ((Zero A) → ((ClZeroTerm A) → A)) 
  evalCl Ze (sing x1) = x1  
  evalCl Ze eCl = (e Ze)  
  evalCl Ze (opCl x1 x2) = ((op Ze) (evalCl Ze x1) (evalCl Ze x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Zero A) → ((Vec A n) → ((OpZeroTerm n) → A))) 
  evalOpB n Ze vars (v x1) = (lookup vars x1)  
  evalOpB n Ze vars eOL = (e Ze)  
  evalOpB n Ze vars (opOL x1 x2) = ((op Ze) (evalOpB n Ze vars x1) (evalOpB n Ze vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Zero A) → ((Vec A n) → ((OpZeroTerm2 n A) → A))) 
  evalOp n Ze vars (v2 x1) = (lookup vars x1)  
  evalOp n Ze vars (sing2 x1) = x1  
  evalOp n Ze vars eOL2 = (e Ze)  
  evalOp n Ze vars (opOL2 x1 x2) = ((op Ze) (evalOp n Ze vars x1) (evalOp n Ze vars x2))  
  inductionB :  (P : (ZeroTerm → Set)) →  ((P eL) → (( (x1 x2 : ZeroTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ( (x : ZeroTerm) → (P x)))) 
  inductionB p pel popl eL = pel  
  inductionB p pel popl (opL x1 x2) = (popl _ _ (inductionB p pel popl x1) (inductionB p pel popl x2))  
  inductionCl :  (A : Set) (P : ((ClZeroTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ((P eCl) → (( (x1 x2 : (ClZeroTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ( (x : (ClZeroTerm A)) → (P x))))) 
  inductionCl _ p psing pecl popcl (sing x1) = (psing x1)  
  inductionCl _ p psing pecl popcl eCl = pecl  
  inductionCl _ p psing pecl popcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing pecl popcl x1) (inductionCl _ p psing pecl popcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpZeroTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ((P eOL) → (( (x1 x2 : (OpZeroTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ( (x : (OpZeroTerm n)) → (P x))))) 
  inductionOpB _ p pv peol popol (v x1) = (pv x1)  
  inductionOpB _ p pv peol popol eOL = peol  
  inductionOpB _ p pv peol popol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv peol popol x1) (inductionOpB _ p pv peol popol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpZeroTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P eOL2) → (( (x1 x2 : (OpZeroTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ( (x : (OpZeroTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 peol2 popol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 peol2 popol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 peol2 popol2 x1) (inductionOp _ _ p pv2 psing2 peol2 popol2 x2))  
  stageB :  (ZeroTerm → (Staged ZeroTerm))
  stageB eL = (Now eL)  
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClZeroTerm A) → (Staged (ClZeroTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpZeroTerm n) → (Staged (OpZeroTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpZeroTerm2 n A) → (Staged (OpZeroTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      eT : (Repr A) 
      opT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 