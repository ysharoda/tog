
module MoufangQuasiGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMoufangQuasiGroup  (A : Set) (op : (A → (A → A))) (linv : (A → (A → A))) (rinv : (A → (A → A))) : Set where 
     field  
      leftCancel : ( {x y : A} → (op x (linv x y)) ≡ y) 
      lefCancelOp : ( {x y : A} → (linv x (op x y)) ≡ y) 
      rightCancel : ( {x y : A} → (op (rinv y x) x) ≡ y) 
      rightCancelOp : ( {x y : A} → (rinv (op y x) x) ≡ y) 
      moufangLaw : ( {e x y z : A} → ((op y e) ≡ y → (op (op (op x y) z) x) ≡ (op x (op y (op (op e z) x)))))  
  
  record MoufangQuasiGroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      linv : (A → (A → A)) 
      rinv : (A → (A → A)) 
      isMoufangQuasiGroup : (IsMoufangQuasiGroup A op linv rinv)  
  
  open MoufangQuasiGroup
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      linvS : (AS → (AS → AS)) 
      rinvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      linvP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftCancelP : ( {xP yP : (Prod A A)} → (opP xP (linvP xP yP)) ≡ yP) 
      lefCancelOpP : ( {xP yP : (Prod A A)} → (linvP xP (opP xP yP)) ≡ yP) 
      rightCancelP : ( {xP yP : (Prod A A)} → (opP (rinvP yP xP) xP) ≡ yP) 
      rightCancelOpP : ( {xP yP : (Prod A A)} → (rinvP (opP yP xP) xP) ≡ yP) 
      moufangLawP : ( {eP xP yP zP : (Prod A A)} → ((opP yP eP) ≡ yP → (opP (opP (opP xP yP) zP) xP) ≡ (opP xP (opP yP (opP (opP eP zP) xP)))))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (MoufangQuasiGroup A1)) (Mo2 : (MoufangQuasiGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Mo1) x1 x2)) ≡ ((op Mo2) (hom x1) (hom x2))) 
      pres-linv : ( {x1 x2 : A1} → (hom ((linv Mo1) x1 x2)) ≡ ((linv Mo2) (hom x1) (hom x2))) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Mo1) x1 x2)) ≡ ((rinv Mo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (MoufangQuasiGroup A1)) (Mo2 : (MoufangQuasiGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2))))) 
      interp-linv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Mo1) x1 x2) ((linv Mo2) y1 y2))))) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Mo1) x1 x2) ((rinv Mo2) y1 y2)))))  
  
  data MoufangQuasiGroupTerm   : Set where 
      opL : (MoufangQuasiGroupTerm → (MoufangQuasiGroupTerm → MoufangQuasiGroupTerm)) 
      linvL : (MoufangQuasiGroupTerm → (MoufangQuasiGroupTerm → MoufangQuasiGroupTerm)) 
      rinvL : (MoufangQuasiGroupTerm → (MoufangQuasiGroupTerm → MoufangQuasiGroupTerm))  
      
  data ClMoufangQuasiGroupTerm  (A : Set) : Set where 
      sing : (A → (ClMoufangQuasiGroupTerm A)) 
      opCl : ((ClMoufangQuasiGroupTerm A) → ((ClMoufangQuasiGroupTerm A) → (ClMoufangQuasiGroupTerm A))) 
      linvCl : ((ClMoufangQuasiGroupTerm A) → ((ClMoufangQuasiGroupTerm A) → (ClMoufangQuasiGroupTerm A))) 
      rinvCl : ((ClMoufangQuasiGroupTerm A) → ((ClMoufangQuasiGroupTerm A) → (ClMoufangQuasiGroupTerm A)))  
      
  data OpMoufangQuasiGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMoufangQuasiGroupTerm n)) 
      opOL : ((OpMoufangQuasiGroupTerm n) → ((OpMoufangQuasiGroupTerm n) → (OpMoufangQuasiGroupTerm n))) 
      linvOL : ((OpMoufangQuasiGroupTerm n) → ((OpMoufangQuasiGroupTerm n) → (OpMoufangQuasiGroupTerm n))) 
      rinvOL : ((OpMoufangQuasiGroupTerm n) → ((OpMoufangQuasiGroupTerm n) → (OpMoufangQuasiGroupTerm n)))  
      
  data OpMoufangQuasiGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMoufangQuasiGroupTerm2 n A)) 
      sing2 : (A → (OpMoufangQuasiGroupTerm2 n A)) 
      opOL2 : ((OpMoufangQuasiGroupTerm2 n A) → ((OpMoufangQuasiGroupTerm2 n A) → (OpMoufangQuasiGroupTerm2 n A))) 
      linvOL2 : ((OpMoufangQuasiGroupTerm2 n A) → ((OpMoufangQuasiGroupTerm2 n A) → (OpMoufangQuasiGroupTerm2 n A))) 
      rinvOL2 : ((OpMoufangQuasiGroupTerm2 n A) → ((OpMoufangQuasiGroupTerm2 n A) → (OpMoufangQuasiGroupTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClMoufangQuasiGroupTerm A) → (ClMoufangQuasiGroupTerm A)) 
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (linvCl x1 x2) = (linvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (rinvCl x1 x2) = (rinvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpMoufangQuasiGroupTerm n) → (OpMoufangQuasiGroupTerm n)) 
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (linvOL x1 x2) = (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (rinvOL x1 x2) = (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpMoufangQuasiGroupTerm2 n A) → (OpMoufangQuasiGroupTerm2 n A)) 
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (linvOL2 x1 x2) = (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MoufangQuasiGroup A) → (MoufangQuasiGroupTerm → A)) 
  evalB Mo (opL x1 x2) = ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo (linvL x1 x2) = ((linv Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo (rinvL x1 x2) = ((rinv Mo) (evalB Mo x1) (evalB Mo x2))  
  evalCl :  {A : Set} →  ((MoufangQuasiGroup A) → ((ClMoufangQuasiGroupTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (opCl x1 x2) = ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo (linvCl x1 x2) = ((linv Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo (rinvCl x1 x2) = ((rinv Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((MoufangQuasiGroup A) → ((Vec A n) → ((OpMoufangQuasiGroupTerm n) → A))) 
  evalOpB Mo vars (v x1) = (lookup vars x1)  
  evalOpB Mo vars (opOL x1 x2) = ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  evalOpB Mo vars (linvOL x1 x2) = ((linv Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  evalOpB Mo vars (rinvOL x1 x2) = ((rinv Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((MoufangQuasiGroup A) → ((Vec A n) → ((OpMoufangQuasiGroupTerm2 n A) → A))) 
  evalOp Mo vars (v2 x1) = (lookup vars x1)  
  evalOp Mo vars (sing2 x1) = x1  
  evalOp Mo vars (opOL2 x1 x2) = ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  evalOp Mo vars (linvOL2 x1 x2) = ((linv Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  evalOp Mo vars (rinvOL2 x1 x2) = ((rinv Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  inductionB :  {P : (MoufangQuasiGroupTerm → Set)} →  (( (x1 x2 : MoufangQuasiGroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 x2 : MoufangQuasiGroupTerm) → ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (( (x1 x2 : MoufangQuasiGroupTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : MoufangQuasiGroupTerm) → (P x))))) 
  inductionB popl plinvl prinvl (opL x1 x2) = (popl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  inductionB popl plinvl prinvl (linvL x1 x2) = (plinvl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  inductionB popl plinvl prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  inductionCl :  {A : Set} {P : ((ClMoufangQuasiGroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMoufangQuasiGroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 x2 : (ClMoufangQuasiGroupTerm A)) → ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (( (x1 x2 : (ClMoufangQuasiGroupTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClMoufangQuasiGroupTerm A)) → (P x)))))) 
  inductionCl psing popcl plinvcl prinvcl (sing x1) = (psing x1)  
  inductionCl psing popcl plinvcl prinvcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  inductionCl psing popcl plinvcl prinvcl (linvCl x1 x2) = (plinvcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  inductionCl psing popcl plinvcl prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpMoufangQuasiGroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMoufangQuasiGroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 x2 : (OpMoufangQuasiGroupTerm n)) → ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (( (x1 x2 : (OpMoufangQuasiGroupTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpMoufangQuasiGroupTerm n)) → (P x)))))) 
  inductionOpB pv popol plinvol prinvol (v x1) = (pv x1)  
  inductionOpB pv popol plinvol prinvol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  inductionOpB pv popol plinvol prinvol (linvOL x1 x2) = (plinvol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  inductionOpB pv popol plinvol prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpMoufangQuasiGroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMoufangQuasiGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 x2 : (OpMoufangQuasiGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (( (x1 x2 : (OpMoufangQuasiGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpMoufangQuasiGroupTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  inductionOp pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2) = (plinvol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  inductionOp pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  stageB :  (MoufangQuasiGroupTerm → (Staged MoufangQuasiGroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (linvL x1 x2) = (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClMoufangQuasiGroupTerm A) → (Staged (ClMoufangQuasiGroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl (linvCl x1 x2) = (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  stageCl (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpMoufangQuasiGroupTerm n) → (Staged (OpMoufangQuasiGroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB (linvOL x1 x2) = (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  stageOpB (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpMoufangQuasiGroupTerm2 n A) → (Staged (OpMoufangQuasiGroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp (linvOL2 x1 x2) = (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  stageOp (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      linvT : ((Repr A) → ((Repr A) → (Repr A))) 
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 