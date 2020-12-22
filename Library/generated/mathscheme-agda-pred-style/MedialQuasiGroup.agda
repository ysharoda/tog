
module MedialQuasiGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMedialQuasiGroup  (A : Set) (op : (A → (A → A))) (linv : (A → (A → A))) (rinv : (A → (A → A))) : Set where 
     field  
      leftCancel : ( {x y : A} → (op x (linv x y)) ≡ y) 
      lefCancelOp : ( {x y : A} → (linv x (op x y)) ≡ y) 
      rightCancel : ( {x y : A} → (op (rinv y x) x) ≡ y) 
      rightCancelOp : ( {x y : A} → (rinv (op y x) x) ≡ y) 
      mediates : ( {w x y z : A} → (op (op x y) (op z w)) ≡ (op (op x z) (op y w)))  
  
  record MedialQuasiGroup  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      linv : (A → (A → A)) 
      rinv : (A → (A → A)) 
      isMedialQuasiGroup : (IsMedialQuasiGroup A op linv rinv)  
  
  open MedialQuasiGroup
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
      mediatesP : ( {wP xP yP zP : (Prod A A)} → (opP (opP xP yP) (opP zP wP)) ≡ (opP (opP xP zP) (opP yP wP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Me1 : (MedialQuasiGroup A1)) (Me2 : (MedialQuasiGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Me1) x1 x2)) ≡ ((op Me2) (hom x1) (hom x2))) 
      pres-linv : ( {x1 x2 : A1} → (hom ((linv Me1) x1 x2)) ≡ ((linv Me2) (hom x1) (hom x2))) 
      pres-rinv : ( {x1 x2 : A1} → (hom ((rinv Me1) x1 x2)) ≡ ((rinv Me2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Me1 : (MedialQuasiGroup A1)) (Me2 : (MedialQuasiGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Me1) x1 x2) ((op Me2) y1 y2))))) 
      interp-linv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Me1) x1 x2) ((linv Me2) y1 y2))))) 
      interp-rinv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Me1) x1 x2) ((rinv Me2) y1 y2)))))  
  
  data MedialQuasiGroupTerm   : Set where 
      opL : (MedialQuasiGroupTerm → (MedialQuasiGroupTerm → MedialQuasiGroupTerm)) 
      linvL : (MedialQuasiGroupTerm → (MedialQuasiGroupTerm → MedialQuasiGroupTerm)) 
      rinvL : (MedialQuasiGroupTerm → (MedialQuasiGroupTerm → MedialQuasiGroupTerm))  
      
  data ClMedialQuasiGroupTerm  (A : Set) : Set where 
      sing : (A → (ClMedialQuasiGroupTerm A)) 
      opCl : ((ClMedialQuasiGroupTerm A) → ((ClMedialQuasiGroupTerm A) → (ClMedialQuasiGroupTerm A))) 
      linvCl : ((ClMedialQuasiGroupTerm A) → ((ClMedialQuasiGroupTerm A) → (ClMedialQuasiGroupTerm A))) 
      rinvCl : ((ClMedialQuasiGroupTerm A) → ((ClMedialQuasiGroupTerm A) → (ClMedialQuasiGroupTerm A)))  
      
  data OpMedialQuasiGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMedialQuasiGroupTerm n)) 
      opOL : ((OpMedialQuasiGroupTerm n) → ((OpMedialQuasiGroupTerm n) → (OpMedialQuasiGroupTerm n))) 
      linvOL : ((OpMedialQuasiGroupTerm n) → ((OpMedialQuasiGroupTerm n) → (OpMedialQuasiGroupTerm n))) 
      rinvOL : ((OpMedialQuasiGroupTerm n) → ((OpMedialQuasiGroupTerm n) → (OpMedialQuasiGroupTerm n)))  
      
  data OpMedialQuasiGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMedialQuasiGroupTerm2 n A)) 
      sing2 : (A → (OpMedialQuasiGroupTerm2 n A)) 
      opOL2 : ((OpMedialQuasiGroupTerm2 n A) → ((OpMedialQuasiGroupTerm2 n A) → (OpMedialQuasiGroupTerm2 n A))) 
      linvOL2 : ((OpMedialQuasiGroupTerm2 n A) → ((OpMedialQuasiGroupTerm2 n A) → (OpMedialQuasiGroupTerm2 n A))) 
      rinvOL2 : ((OpMedialQuasiGroupTerm2 n A) → ((OpMedialQuasiGroupTerm2 n A) → (OpMedialQuasiGroupTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClMedialQuasiGroupTerm A) → (ClMedialQuasiGroupTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (linvCl x1 x2) = (linvCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (rinvCl x1 x2) = (rinvCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpMedialQuasiGroupTerm n) → (OpMedialQuasiGroupTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (linvOL x1 x2) = (linvOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (rinvOL x1 x2) = (rinvOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpMedialQuasiGroupTerm2 n A) → (OpMedialQuasiGroupTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (linvOL2 x1 x2) = (linvOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (rinvOL2 x1 x2) = (rinvOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MedialQuasiGroup A) → (MedialQuasiGroupTerm → A)) 
  evalB Me (opL x1 x2) = ((op Me) (evalB Me x1) (evalB Me x2))  
  evalB Me (linvL x1 x2) = ((linv Me) (evalB Me x1) (evalB Me x2))  
  evalB Me (rinvL x1 x2) = ((rinv Me) (evalB Me x1) (evalB Me x2))  
  evalCl :  {A : Set} →  ((MedialQuasiGroup A) → ((ClMedialQuasiGroupTerm A) → A)) 
  evalCl Me (sing x1) = x1  
  evalCl Me (opCl x1 x2) = ((op Me) (evalCl Me x1) (evalCl Me x2))  
  evalCl Me (linvCl x1 x2) = ((linv Me) (evalCl Me x1) (evalCl Me x2))  
  evalCl Me (rinvCl x1 x2) = ((rinv Me) (evalCl Me x1) (evalCl Me x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((MedialQuasiGroup A) → ((Vec A n) → ((OpMedialQuasiGroupTerm n) → A))) 
  evalOpB n Me vars (v x1) = (lookup vars x1)  
  evalOpB n Me vars (opOL x1 x2) = ((op Me) (evalOpB n Me vars x1) (evalOpB n Me vars x2))  
  evalOpB n Me vars (linvOL x1 x2) = ((linv Me) (evalOpB n Me vars x1) (evalOpB n Me vars x2))  
  evalOpB n Me vars (rinvOL x1 x2) = ((rinv Me) (evalOpB n Me vars x1) (evalOpB n Me vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((MedialQuasiGroup A) → ((Vec A n) → ((OpMedialQuasiGroupTerm2 n A) → A))) 
  evalOp n Me vars (v2 x1) = (lookup vars x1)  
  evalOp n Me vars (sing2 x1) = x1  
  evalOp n Me vars (opOL2 x1 x2) = ((op Me) (evalOp n Me vars x1) (evalOp n Me vars x2))  
  evalOp n Me vars (linvOL2 x1 x2) = ((linv Me) (evalOp n Me vars x1) (evalOp n Me vars x2))  
  evalOp n Me vars (rinvOL2 x1 x2) = ((rinv Me) (evalOp n Me vars x1) (evalOp n Me vars x2))  
  inductionB :  (P : (MedialQuasiGroupTerm → Set)) →  (( (x1 x2 : MedialQuasiGroupTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 x2 : MedialQuasiGroupTerm) → ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (( (x1 x2 : MedialQuasiGroupTerm) → ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ( (x : MedialQuasiGroupTerm) → (P x))))) 
  inductionB p popl plinvl prinvl (opL x1 x2) = (popl _ _ (inductionB p popl plinvl prinvl x1) (inductionB p popl plinvl prinvl x2))  
  inductionB p popl plinvl prinvl (linvL x1 x2) = (plinvl _ _ (inductionB p popl plinvl prinvl x1) (inductionB p popl plinvl prinvl x2))  
  inductionB p popl plinvl prinvl (rinvL x1 x2) = (prinvl _ _ (inductionB p popl plinvl prinvl x1) (inductionB p popl plinvl prinvl x2))  
  inductionCl :  (A : Set) (P : ((ClMedialQuasiGroupTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMedialQuasiGroupTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 x2 : (ClMedialQuasiGroupTerm A)) → ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (( (x1 x2 : (ClMedialQuasiGroupTerm A)) → ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ( (x : (ClMedialQuasiGroupTerm A)) → (P x)))))) 
  inductionCl _ p psing popcl plinvcl prinvcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl plinvcl prinvcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1) (inductionCl _ p psing popcl plinvcl prinvcl x2))  
  inductionCl _ p psing popcl plinvcl prinvcl (linvCl x1 x2) = (plinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1) (inductionCl _ p psing popcl plinvcl prinvcl x2))  
  inductionCl _ p psing popcl plinvcl prinvcl (rinvCl x1 x2) = (prinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1) (inductionCl _ p psing popcl plinvcl prinvcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpMedialQuasiGroupTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMedialQuasiGroupTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 x2 : (OpMedialQuasiGroupTerm n)) → ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (( (x1 x2 : (OpMedialQuasiGroupTerm n)) → ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ( (x : (OpMedialQuasiGroupTerm n)) → (P x)))))) 
  inductionOpB _ p pv popol plinvol prinvol (v x1) = (pv x1)  
  inductionOpB _ p pv popol plinvol prinvol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol plinvol prinvol x1) (inductionOpB _ p pv popol plinvol prinvol x2))  
  inductionOpB _ p pv popol plinvol prinvol (linvOL x1 x2) = (plinvol _ _ (inductionOpB _ p pv popol plinvol prinvol x1) (inductionOpB _ p pv popol plinvol prinvol x2))  
  inductionOpB _ p pv popol plinvol prinvol (rinvOL x1 x2) = (prinvol _ _ (inductionOpB _ p pv popol plinvol prinvol x1) (inductionOpB _ p pv popol plinvol prinvol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpMedialQuasiGroupTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMedialQuasiGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 x2 : (OpMedialQuasiGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (( (x1 x2 : (OpMedialQuasiGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ( (x : (OpMedialQuasiGroupTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2) = (plinvol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2) = (prinvol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  stageB :  (MedialQuasiGroupTerm → (Staged MedialQuasiGroupTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (linvL x1 x2) = (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  stageB (rinvL x1 x2) = (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClMedialQuasiGroupTerm A) → (Staged (ClMedialQuasiGroupTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (linvCl x1 x2) = (stage2 linvCl (codeLift2 linvCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (rinvCl x1 x2) = (stage2 rinvCl (codeLift2 rinvCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpMedialQuasiGroupTerm n) → (Staged (OpMedialQuasiGroupTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (linvOL x1 x2) = (stage2 linvOL (codeLift2 linvOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (rinvOL x1 x2) = (stage2 rinvOL (codeLift2 rinvOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpMedialQuasiGroupTerm2 n A) → (Staged (OpMedialQuasiGroupTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (linvOL2 x1 x2) = (stage2 linvOL2 (codeLift2 linvOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (rinvOL2 x1 x2) = (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      linvT : ((Repr A) → ((Repr A) → (Repr A))) 
      rinvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 