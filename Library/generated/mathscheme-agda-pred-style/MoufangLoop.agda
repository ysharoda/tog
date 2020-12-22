
module MoufangLoop   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMoufangLoop  (A : Set) (op : (A → (A → A))) (e : A) (linv : (A → (A → A))) (rinv : (A → (A → A))) : Set where 
     field  
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      leftCancel : ( {x y : A} → (op x (linv x y)) ≡ y) 
      lefCancelOp : ( {x y : A} → (linv x (op x y)) ≡ y) 
      rightCancel : ( {x y : A} → (op (rinv y x) x) ≡ y) 
      rightCancelOp : ( {x y : A} → (rinv (op y x) x) ≡ y) 
      moufangId : ( {x y z : A} → (op (op z x) (op y z)) ≡ (op (op z (op x y)) z))  
  
  record MoufangLoop  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      linv : (A → (A → A)) 
      rinv : (A → (A → A)) 
      isMoufangLoop : (IsMoufangLoop A op e linv rinv)  
  
  open MoufangLoop
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS 
      linvS : (AS → (AS → AS)) 
      rinvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      linvP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      lunit_eP : ( {xP : (Prod A A)} → (opP eP xP) ≡ xP) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      leftCancelP : ( {xP yP : (Prod A A)} → (opP xP (linvP xP yP)) ≡ yP) 
      lefCancelOpP : ( {xP yP : (Prod A A)} → (linvP xP (opP xP yP)) ≡ yP) 
      rightCancelP : ( {xP yP : (Prod A A)} → (opP (rinvP yP xP) xP) ≡ yP) 
      rightCancelOpP : ( {xP yP : (Prod A A)} → (rinvP (opP yP xP) xP) ≡ yP) 
      moufangIdP : ( {xP yP zP : (Prod A A)} → (opP (opP zP xP) (opP yP zP)) ≡ (opP (opP zP (opP xP yP)) zP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (MoufangLoop A1)) (Mo2 : (MoufangLoop A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Mo1) x1 x2)) ≡ ((op Mo2) (hom x1) (hom x2))) 
      pres-e : (hom (e Mo1)) ≡ (e Mo2) 
      pres-linv : ( {x1 x2 : A1} → (hom ((linv Mo1) x1 x2)) ≡ ((linv Mo2) (hom x1) (hom x2))) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Mo1) x1 x2)) ≡ ((rinv Mo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (MoufangLoop A1)) (Mo2 : (MoufangLoop A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2))))) 
      interp-e : (interp (e Mo1) (e Mo2)) 
      interp-linv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Mo1) x1 x2) ((linv Mo2) y1 y2))))) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Mo1) x1 x2) ((rinv Mo2) y1 y2)))))  
  
  data MoufangLoopLTerm   : Set where 
      opL : (MoufangLoopLTerm → (MoufangLoopLTerm → MoufangLoopLTerm)) 
      eL : MoufangLoopLTerm 
      linvL : (MoufangLoopLTerm → (MoufangLoopLTerm → MoufangLoopLTerm)) 
      rinvL : (MoufangLoopLTerm → (MoufangLoopLTerm → MoufangLoopLTerm))  
      
  data ClMoufangLoopClTerm  (A : Set) : Set where 
      sing : (A → (ClMoufangLoopClTerm A)) 
      opCl : ((ClMoufangLoopClTerm A) → ((ClMoufangLoopClTerm A) → (ClMoufangLoopClTerm A))) 
      eCl : (ClMoufangLoopClTerm A) 
      linvCl : ((ClMoufangLoopClTerm A) → ((ClMoufangLoopClTerm A) → (ClMoufangLoopClTerm A))) 
      rinvCl : ((ClMoufangLoopClTerm A) → ((ClMoufangLoopClTerm A) → (ClMoufangLoopClTerm A)))  
      
  data OpMoufangLoopOLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMoufangLoopOLTerm n)) 
      opOL : ((OpMoufangLoopOLTerm n) → ((OpMoufangLoopOLTerm n) → (OpMoufangLoopOLTerm n))) 
      eOL : (OpMoufangLoopOLTerm n) 
      linvOL : ((OpMoufangLoopOLTerm n) → ((OpMoufangLoopOLTerm n) → (OpMoufangLoopOLTerm n))) 
      rinvOL : ((OpMoufangLoopOLTerm n) → ((OpMoufangLoopOLTerm n) → (OpMoufangLoopOLTerm n)))  
      
  data OpMoufangLoopOL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMoufangLoopOL2Term2 n A)) 
      sing2 : (A → (OpMoufangLoopOL2Term2 n A)) 
      opOL2 : ((OpMoufangLoopOL2Term2 n A) → ((OpMoufangLoopOL2Term2 n A) → (OpMoufangLoopOL2Term2 n A))) 
      eOL2 : (OpMoufangLoopOL2Term2 n A) 
      linvOL2 : ((OpMoufangLoopOL2Term2 n A) → ((OpMoufangLoopOL2Term2 n A) → (OpMoufangLoopOL2Term2 n A))) 
      rinvOL2 : ((OpMoufangLoopOL2Term2 n A) → ((OpMoufangLoopOL2Term2 n A) → (OpMoufangLoopOL2Term2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMoufangLoopClTerm A) → (ClMoufangLoopClTerm A)) 
  simplifyCl _ (opCl eCl x) = x  
  simplifyCl _ (opCl x eCl) = x  
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ eCl = eCl  
  simplifyCl _ (linvCl x1 x2) = (linvCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (rinvCl x1 x2) = (rinvCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMoufangLoopOLTerm n) → (OpMoufangLoopOLTerm n)) 
  simplifyOpB _ (opOL eOL x) = x  
  simplifyOpB _ (opOL x eOL) = x  
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ eOL = eOL  
  simplifyOpB _ (linvOL x1 x2) = (linvOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (rinvOL x1 x2) = (rinvOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMoufangLoopOL2Term2 n A) → (OpMoufangLoopOL2Term2 n A)) 
  simplifyOp _ _ (opOL2 eOL2 x) = x  
  simplifyOp _ _ (opOL2 x eOL2) = x  
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ eOL2 = eOL2  
  simplifyOp _ _ (linvOL2 x1 x2) = (linvOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MoufangLoop A) → (MoufangLoopLTerm → A)) 
  evalB Mo (opL x1 x2) = ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo eL = (e Mo)  
  evalB Mo (linvL x1 x2) = ((linv Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo (rinvL x1 x2) = ((rinv Mo) (evalB Mo x1) (evalB Mo x2))  
  evalCl :  {A : Set} →  ((MoufangLoop A) → ((ClMoufangLoopClTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (opCl x1 x2) = ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo eCl = (e Mo)  
  evalCl Mo (linvCl x1 x2) = ((linv Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo (rinvCl x1 x2) = ((rinv Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MoufangLoop A) → ((Vec A n) → ((OpMoufangLoopOLTerm n) → A))) 
  evalOpB n Mo vars (v x1) = (lookup vars x1)  
  evalOpB n Mo vars (opOL x1 x2) = ((op Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOpB n Mo vars eOL = (e Mo)  
  evalOpB n Mo vars (linvOL x1 x2) = ((linv Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOpB n Mo vars (rinvOL x1 x2) = ((rinv Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MoufangLoop A) → ((Vec A n) → ((OpMoufangLoopOL2Term2 n A) → A))) 
  evalOp n Mo vars (v2 x1) = (lookup vars x1)  
  evalOp n Mo vars (sing2 x1) = x1  
  evalOp n Mo vars (opOL2 x1 x2) = ((op Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  evalOp n Mo vars eOL2 = (e Mo)  
  evalOp n Mo vars (linvOL2 x1 x2) = ((linv Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  evalOp n Mo vars (rinvOL2 x1 x2) = ((rinv Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  inductionB :  (P : (MoufangLoopLTerm → Set)) →  (( (x1 x2 : MoufangLoopLTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (( (x1 x2 : MoufangLoopLTerm) → ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (( (x1 x2 : MoufangLoopLTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : MoufangLoopLTerm) → (P x)))))) 
  inductionB p popl pel plinvl prinvl (opL x1 x2) = (popl _ _ (inductionB p popl pel plinvl prinvl x1) (inductionB p popl pel plinvl prinvl x2))  
  inductionB p popl pel plinvl prinvl eL = pel  
  inductionB p popl pel plinvl prinvl (linvL x1 x2) = (plinvl _ _ (inductionB p popl pel plinvl prinvl x1) (inductionB p popl pel plinvl prinvl x2))  
  inductionB p popl pel plinvl prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB p popl pel plinvl prinvl x1) (inductionB p popl pel plinvl prinvl x2))  
  inductionCl :  (A : Set) (P : ((ClMoufangLoopClTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMoufangLoopClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (( (x1 x2 : (ClMoufangLoopClTerm A)) → ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (( (x1 x2 : (ClMoufangLoopClTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClMoufangLoopClTerm A)) → (P x))))))) 
  inductionCl _ p psing popcl pecl plinvcl prinvcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2))  
  inductionCl _ p psing popcl pecl plinvcl prinvcl eCl = pecl  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (linvCl x1 x2) = (plinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2))  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMoufangLoopOLTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMoufangLoopOLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (( (x1 x2 : (OpMoufangLoopOLTerm n)) → ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (( (x1 x2 : (OpMoufangLoopOLTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpMoufangLoopOLTerm n)) → (P x))))))) 
  inductionOpB _ p pv popol peol plinvol prinvol (v x1) = (pv x1)  
  inductionOpB _ p pv popol peol plinvol prinvol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol peol plinvol prinvol x1) (inductionOpB _ p pv popol peol plinvol prinvol x2))  
  inductionOpB _ p pv popol peol plinvol prinvol eOL = peol  
  inductionOpB _ p pv popol peol plinvol prinvol (linvOL x1 x2) = (plinvol _ _ (inductionOpB _ p pv popol peol plinvol prinvol x1) (inductionOpB _ p pv popol peol plinvol prinvol x2))  
  inductionOpB _ p pv popol peol plinvol prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB _ p pv popol peol plinvol prinvol x1) (inductionOpB _ p pv popol peol plinvol prinvol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMoufangLoopOL2Term2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMoufangLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (( (x1 x2 : (OpMoufangLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (( (x1 x2 : (OpMoufangLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpMoufangLoopOL2Term2 n A)) → (P x)))))))) 
  inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 eOL2 = peol2  
  inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (linvOL2 x1 x2) = (plinvol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2))  
  stageB :  (MoufangLoopLTerm → (Staged MoufangLoopLTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageB (linvL x1 x2) = (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMoufangLoopClTerm A) → (Staged (ClMoufangLoopClTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ eCl = (Now eCl)  
  stageCl _ (linvCl x1 x2) = (stage2 linvCl (codeLift2 linvCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMoufangLoopOLTerm n) → (Staged (OpMoufangLoopOLTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ eOL = (Now eOL)  
  stageOpB _ (linvOL x1 x2) = (stage2 linvOL (codeLift2 linvOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMoufangLoopOL2Term2 n A) → (Staged (OpMoufangLoopOL2Term2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ eOL2 = (Now eOL2)  
  stageOp _ _ (linvOL2 x1 x2) = (stage2 linvOL2 (codeLift2 linvOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A) 
      linvT : ((Repr A) → ((Repr A) → (Repr A))) 
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 