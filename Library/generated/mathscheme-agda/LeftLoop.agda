
module LeftLoop   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftLoop  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      e : A 
      runit_e : ( {x : A} → (op x e) ≡ x) 
      linv : (A → (A → A)) 
      leftCancel : ( {x y : A} → (op x (linv x y)) ≡ y) 
      lefCancelOp : ( {x y : A} → (linv x (op x y)) ≡ y)  
  
  open LeftLoop
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      eS : AS 
      linvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      eP : (Prod A A) 
      linvP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      runit_eP : ( {xP : (Prod A A)} → (opP xP eP) ≡ xP) 
      leftCancelP : ( {xP yP : (Prod A A)} → (opP xP (linvP xP yP)) ≡ yP) 
      lefCancelOpP : ( {xP yP : (Prod A A)} → (linvP xP (opP xP yP)) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftLoop A1)) (Le2 : (LeftLoop A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2))) 
      pres-e : (hom (e Le1)) ≡ (e Le2) 
      pres-linv : ( {x1 x2 : A1} → (hom ((linv Le1) x1 x2)) ≡ ((linv Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftLoop A1)) (Le2 : (LeftLoop A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2))))) 
      interp-e : (interp (e Le1) (e Le2)) 
      interp-linv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2)))))  
  
  data LeftLoopLTerm   : Set where 
      opL : (LeftLoopLTerm → (LeftLoopLTerm → LeftLoopLTerm)) 
      eL : LeftLoopLTerm 
      linvL : (LeftLoopLTerm → (LeftLoopLTerm → LeftLoopLTerm))  
      
  data ClLeftLoopClTerm  (A : Set) : Set where 
      sing : (A → (ClLeftLoopClTerm A)) 
      opCl : ((ClLeftLoopClTerm A) → ((ClLeftLoopClTerm A) → (ClLeftLoopClTerm A))) 
      eCl : (ClLeftLoopClTerm A) 
      linvCl : ((ClLeftLoopClTerm A) → ((ClLeftLoopClTerm A) → (ClLeftLoopClTerm A)))  
      
  data OpLeftLoopOLTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftLoopOLTerm n)) 
      opOL : ((OpLeftLoopOLTerm n) → ((OpLeftLoopOLTerm n) → (OpLeftLoopOLTerm n))) 
      eOL : (OpLeftLoopOLTerm n) 
      linvOL : ((OpLeftLoopOLTerm n) → ((OpLeftLoopOLTerm n) → (OpLeftLoopOLTerm n)))  
      
  data OpLeftLoopOL2Term2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftLoopOL2Term2 n A)) 
      sing2 : (A → (OpLeftLoopOL2Term2 n A)) 
      opOL2 : ((OpLeftLoopOL2Term2 n A) → ((OpLeftLoopOL2Term2 n A) → (OpLeftLoopOL2Term2 n A))) 
      eOL2 : (OpLeftLoopOL2Term2 n A) 
      linvOL2 : ((OpLeftLoopOL2Term2 n A) → ((OpLeftLoopOL2Term2 n A) → (OpLeftLoopOL2Term2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLeftLoopClTerm A) → (ClLeftLoopClTerm A)) 
  simplifyCl (opCl x eCl) = x  
  simplifyCl (opCl x1 x2) = (opCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl eCl = eCl  
  simplifyCl (linvCl x1 x2) = (linvCl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLeftLoopOLTerm n) → (OpLeftLoopOLTerm n)) 
  simplifyOpB (opOL x eOL) = x  
  simplifyOpB (opOL x1 x2) = (opOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB eOL = eOL  
  simplifyOpB (linvOL x1 x2) = (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLeftLoopOL2Term2 n A) → (OpLeftLoopOL2Term2 n A)) 
  simplifyOp (opOL2 x eOL2) = x  
  simplifyOp (opOL2 x1 x2) = (opOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp eOL2 = eOL2  
  simplifyOp (linvOL2 x1 x2) = (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftLoop A) → (LeftLoopLTerm → A)) 
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalB Le eL = (e Le)  
  evalB Le (linvL x1 x2) = ((linv Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftLoop A) → ((ClLeftLoopClTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalCl Le eCl = (e Le)  
  evalCl Le (linvCl x1 x2) = ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((LeftLoop A) → ((Vec A n) → ((OpLeftLoopOLTerm n) → A))) 
  evalOpB Le vars (v x1) = (lookup vars x1)  
  evalOpB Le vars (opOL x1 x2) = ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOpB Le vars eOL = (e Le)  
  evalOpB Le vars (linvOL x1 x2) = ((linv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((LeftLoop A) → ((Vec A n) → ((OpLeftLoopOL2Term2 n A) → A))) 
  evalOp Le vars (v2 x1) = (lookup vars x1)  
  evalOp Le vars (sing2 x1) = x1  
  evalOp Le vars (opOL2 x1 x2) = ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  evalOp Le vars eOL2 = (e Le)  
  evalOp Le vars (linvOL2 x1 x2) = ((linv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  inductionB :  {P : (LeftLoopLTerm → Set)} →  (( (x1 x2 : LeftLoopLTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (( (x1 x2 : LeftLoopLTerm) → ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ( (x : LeftLoopLTerm) → (P x))))) 
  inductionB popl pel plinvl (opL x1 x2) = (popl _ _ (inductionB popl pel plinvl x1) (inductionB popl pel plinvl x2))  
  inductionB popl pel plinvl eL = pel  
  inductionB popl pel plinvl (linvL x1 x2) = (plinvl _ _ (inductionB popl pel plinvl x1) (inductionB popl pel plinvl x2))  
  inductionCl :  {A : Set} {P : ((ClLeftLoopClTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftLoopClTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (( (x1 x2 : (ClLeftLoopClTerm A)) → ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ( (x : (ClLeftLoopClTerm A)) → (P x)))))) 
  inductionCl psing popcl pecl plinvcl (sing x1) = (psing x1)  
  inductionCl psing popcl pecl plinvcl (opCl x1 x2) = (popcl _ _ (inductionCl psing popcl pecl plinvcl x1) (inductionCl psing popcl pecl plinvcl x2))  
  inductionCl psing popcl pecl plinvcl eCl = pecl  
  inductionCl psing popcl pecl plinvcl (linvCl x1 x2) = (plinvcl _ _ (inductionCl psing popcl pecl plinvcl x1) (inductionCl psing popcl pecl plinvcl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLeftLoopOLTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftLoopOLTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (( (x1 x2 : (OpLeftLoopOLTerm n)) → ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ( (x : (OpLeftLoopOLTerm n)) → (P x)))))) 
  inductionOpB pv popol peol plinvol (v x1) = (pv x1)  
  inductionOpB pv popol peol plinvol (opOL x1 x2) = (popol _ _ (inductionOpB pv popol peol plinvol x1) (inductionOpB pv popol peol plinvol x2))  
  inductionOpB pv popol peol plinvol eOL = peol  
  inductionOpB pv popol peol plinvol (linvOL x1 x2) = (plinvol _ _ (inductionOpB pv popol peol plinvol x1) (inductionOpB pv popol peol plinvol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLeftLoopOL2Term2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (( (x1 x2 : (OpLeftLoopOL2Term2 n A)) → ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ( (x : (OpLeftLoopOL2Term2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 popol2 peol2 plinvol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 x2))  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 eOL2 = peol2  
  inductionOp pv2 psing2 popol2 peol2 plinvol2 (linvOL2 x1 x2) = (plinvol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 x2))  
  stageB :  (LeftLoopLTerm → (Staged LeftLoopLTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB eL = (Now eL)  
  stageB (linvL x1 x2) = (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLeftLoopClTerm A) → (Staged (ClLeftLoopClTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  stageCl eCl = (Now eCl)  
  stageCl (linvCl x1 x2) = (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLeftLoopOLTerm n) → (Staged (OpLeftLoopOLTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  stageOpB eOL = (Now eOL)  
  stageOpB (linvOL x1 x2) = (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLeftLoopOL2Term2 n A) → (Staged (OpLeftLoopOL2Term2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  stageOp eOL2 = (Now eOL2)  
  stageOp (linvOL2 x1 x2) = (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      eT : (Repr A) 
      linvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 