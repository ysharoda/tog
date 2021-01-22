
module Loop   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Loop  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      lunit_e : ( {x : A} → (op e x) ≡ x) 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      linv : (A → (A → A)) 
      leftCancel : ( {x y : A} → (op x (linv x y)) ≡ y) 
      lefCancelOp : ( {x y : A} → (linv x (op x y)) ≡ y) 
      rinv : (A → (A → A)) 
      rightCancel : ( {x y : A} → (op (rinv y x) x) ≡ y) 
      rightCancelOp : ( {x y : A} → (rinv (op y x) x) ≡ y)  
  
  open Loop
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
  
  record Hom  {A1 : Set} {A2 : Set} (Lo1 : (Loop A1)) (Lo2 : (Loop A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Lo1) x1 x2)) ≡ ((op Lo2) (hom x1) (hom x2))) 
      pres-e : (hom (e Lo1)) ≡ (e Lo2) 
      pres-linv : ( {x1 x2 : A1} → (hom ((linv Lo1) x1 x2)) ≡ ((linv Lo2) (hom x1) (hom x2))) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Lo1) x1 x2)) ≡ ((rinv Lo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Lo1 : (Loop A1)) (Lo2 : (Loop A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Lo1) x1 x2) ((op Lo2) y1 y2))))) 
      interp-e : (interp (e Lo1) (e Lo2)) 
      interp-linv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Lo1) x1 x2) ((linv Lo2) y1 y2))))) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Lo1) x1 x2) ((rinv Lo2) y1 y2)))))  
  
  data LoopLTerm   : Set where 
      opL : (LoopLTerm → (LoopLTerm → LoopLTerm)) 
      eL : LoopLTerm 
      linvL : (LoopLTerm → (LoopLTerm → LoopLTerm)) 
      rinvL : (LoopLTerm → (LoopLTerm → LoopLTerm))  
      
  data ClLoopClTerm  (A : Set) : Set where 
      sing : (A → (ClLoopClTerm A)) 
      opCl : ((ClLoopClTerm A) → ((ClLoopClTerm A) → (ClLoopClTerm A))) 
      eCl : (ClLoopClTerm A) 
      linvCl : ((ClLoopClTerm A) → ((ClLoopClTerm A) → (ClLoopClTerm A))) 
      rinvCl : ((ClLoopClTerm A) → ((ClLoopClTerm A) → (ClLoopClTerm A)))  
      
  data OpLoopOLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLoopOLTerm n)) 
      opOL : ((OpLoopOLTerm n) → ((OpLoopOLTerm n) → (OpLoopOLTerm n))) 
      eOL : (OpLoopOLTerm n) 
      linvOL : ((OpLoopOLTerm n) → ((OpLoopOLTerm n) → (OpLoopOLTerm n))) 
      rinvOL : ((OpLoopOLTerm n) → ((OpLoopOLTerm n) → (OpLoopOLTerm n)))  
      
  data OpLoopOL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLoopOL2Term2 n A)) 
      sing2 : (A → (OpLoopOL2Term2 n A)) 
      opOL2 : ((OpLoopOL2Term2 n A) → ((OpLoopOL2Term2 n A) → (OpLoopOL2Term2 n A))) 
      eOL2 : (OpLoopOL2Term2 n A) 
      linvOL2 : ((OpLoopOL2Term2 n A) → ((OpLoopOL2Term2 n A) → (OpLoopOL2Term2 n A))) 
      rinvOL2 : ((OpLoopOL2Term2 n A) → ((OpLoopOL2Term2 n A) → (OpLoopOL2Term2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLoopClTerm A) → (ClLoopClTerm A)) 
  simplifyCl (opCl eCl x) = x  
  simplifyCl (opCl x eCl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (linvCl x1 x2) = (linvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (rinvCl x1 x2) = (rinvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLoopOLTerm n) → (OpLoopOLTerm n)) 
  simplifyOpB (opOL eOL x) = x  
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (linvOL x1 x2) = (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (rinvOL x1 x2) = (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLoopOL2Term2 n A) → (OpLoopOL2Term2 n A)) 
  simplifyOp (opOL2 eOL2 x) = x  
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (linvOL2 x1 x2) = (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Loop A) → (LoopLTerm → A)) 
  evalB Lo (opL x1 x2) = ((op Lo) (evalB Lo x1) (evalB Lo x2))  
  evalB Lo eL = (e Lo)  
  evalB Lo (linvL x1 x2) = ((linv Lo) (evalB Lo x1) (evalB Lo x2))  
  evalB Lo (rinvL x1 x2) = ((rinv Lo) (evalB Lo x1) (evalB Lo x2))  
  evalCl :  {A : Set} →  ((Loop A) → ((ClLoopClTerm A) → A)) 
  evalCl Lo (sing x1) = x1  
  evalCl Lo (opCl x1 x2) = ((op Lo) (evalCl Lo x1) (evalCl Lo x2))  
  evalCl Lo eCl = (e Lo)  
  evalCl Lo (linvCl x1 x2) = ((linv Lo) (evalCl Lo x1) (evalCl Lo x2))  
  evalCl Lo (rinvCl x1 x2) = ((rinv Lo) (evalCl Lo x1) (evalCl Lo x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Loop A) → ((Vec A n) → ((OpLoopOLTerm n) → A))) 
  evalOpB Lo vars (v x1) = (lookup vars x1)  
  evalOpB Lo vars (opOL x1 x2) = ((op Lo) (evalOpB Lo vars x1) (evalOpB Lo vars x2))  
  evalOpB Lo vars eOL = (e Lo)  
  evalOpB Lo vars (linvOL x1 x2) = ((linv Lo) (evalOpB Lo vars x1) (evalOpB Lo vars x2))  
  evalOpB Lo vars (rinvOL x1 x2) = ((rinv Lo) (evalOpB Lo vars x1) (evalOpB Lo vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Loop A) → ((Vec A n) → ((OpLoopOL2Term2 n A) → A))) 
  evalOp Lo vars (v2 x1) = (lookup vars x1)  
  evalOp Lo vars (sing2 x1) = x1  
  evalOp Lo vars (opOL2 x1 x2) = ((op Lo) (evalOp Lo vars x1) (evalOp Lo vars x2))  
  evalOp Lo vars eOL2 = (e Lo)  
  evalOp Lo vars (linvOL2 x1 x2) = ((linv Lo) (evalOp Lo vars x1) (evalOp Lo vars x2))  
  evalOp Lo vars (rinvOL2 x1 x2) = ((rinv Lo) (evalOp Lo vars x1) (evalOp Lo vars x2))  
  inductionB :  {P : (LoopLTerm → Set)} →  (( (x1 x2 : LoopLTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (( (x1 x2 : LoopLTerm) → ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (( (x1 x2 : LoopLTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : LoopLTerm) → (P x)))))) 
  inductionB popl pel plinvl prinvl (opL x1 x2) = (popl _ _ (inductionB popl pel plinvl prinvl x1) (inductionB popl pel plinvl prinvl x2))  
  inductionB popl pel plinvl prinvl eL = pel  
  inductionB popl pel plinvl prinvl (linvL x1 x2) = (plinvl _ _ (inductionB popl pel plinvl prinvl x1) (inductionB popl pel plinvl prinvl x2))  
  inductionB popl pel plinvl prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB popl pel plinvl prinvl x1) (inductionB popl pel plinvl prinvl x2))  
  inductionCl :  {A : Set} {P : ((ClLoopClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLoopClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (( (x1 x2 : (ClLoopClTerm A)) → ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (( (x1 x2 : (ClLoopClTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClLoopClTerm A)) → (P x))))))) 
  inductionCl psing popcl pecl plinvcl prinvcl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl plinvcl prinvcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl plinvcl prinvcl x1) (inductionCl psing popcl pecl plinvcl prinvcl x2))  
  inductionCl psing popcl pecl plinvcl prinvcl eCl = pecl  
  inductionCl psing popcl pecl plinvcl prinvcl (linvCl x1 x2) = (plinvcl _ _ (inductionCl psing popcl pecl plinvcl prinvcl x1) (inductionCl psing popcl pecl plinvcl prinvcl x2))  
  inductionCl psing popcl pecl plinvcl prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl psing popcl pecl plinvcl prinvcl x1) (inductionCl psing popcl pecl plinvcl prinvcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLoopOLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLoopOLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (( (x1 x2 : (OpLoopOLTerm n)) → ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (( (x1 x2 : (OpLoopOLTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpLoopOLTerm n)) → (P x))))))) 
  inductionOpB pv popol peol plinvol prinvol (v x1) = (pv x1)  
  inductionOpB pv popol peol plinvol prinvol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol plinvol prinvol x1) (inductionOpB pv popol peol plinvol prinvol x2))  
  inductionOpB pv popol peol plinvol prinvol eOL = peol  
  inductionOpB pv popol peol plinvol prinvol (linvOL x1 x2) = (plinvol _ _ (inductionOpB pv popol peol plinvol prinvol x1) (inductionOpB pv popol peol plinvol prinvol x2))  
  inductionOpB pv popol peol plinvol prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB pv popol peol plinvol prinvol x1) (inductionOpB pv popol peol plinvol prinvol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLoopOL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (( (x1 x2 : (OpLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (( (x1 x2 : (OpLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpLoopOL2Term2 n A)) → (P x)))))))) 
  inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 eOL2 = peol2  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 (linvOL2 x1 x2) = (plinvol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2))  
  stageB :  (LoopLTerm → (Staged LoopLTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageB (linvL x1 x2) = (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLoopClTerm A) → (Staged (ClLoopClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageCl (linvCl x1 x2) = (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  stageCl (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLoopOLTerm n) → (Staged (OpLoopOLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOpB (linvOL x1 x2) = (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  stageOpB (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLoopOL2Term2 n A) → (Staged (OpLoopOL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (linvOL2 x1 x2) = (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  stageOp (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A) 
      linvT : ((Repr A) → ((Repr A) → (Repr A))) 
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 