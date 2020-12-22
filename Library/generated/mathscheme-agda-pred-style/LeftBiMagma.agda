
module LeftBiMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftBiMagma  (A : Set) (op : (A → (A → A))) (linv : (A → (A → A))) : Set where 
    
  record LeftBiMagma  (A : Set) : Set where 
     field  
      op : (A → (A → A)) 
      linv : (A → (A → A)) 
      isLeftBiMagma : (IsLeftBiMagma A op linv)  
  
  open LeftBiMagma
  record Sig  (AS : Set) : Set where 
     field  
      opS : (AS → (AS → AS)) 
      linvS : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      opP : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      linvP : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftBiMagma A1)) (Le2 : (LeftBiMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-op : ( {x1 x2 : A1} → (hom ((op Le1) x1 x2)) ≡ ((op Le2) (hom x1) (hom x2))) 
      pres-linv : ( {x1 x2 : A1} → (hom ((linv Le1) x1 x2)) ≡ ((linv Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftBiMagma A1)) (Le2 : (LeftBiMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-op : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2))))) 
      interp-linv : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2)))))  
  
  data LeftBiMagmaTerm   : Set where 
      opL : (LeftBiMagmaTerm → (LeftBiMagmaTerm → LeftBiMagmaTerm)) 
      linvL : (LeftBiMagmaTerm → (LeftBiMagmaTerm → LeftBiMagmaTerm))  
      
  data ClLeftBiMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClLeftBiMagmaTerm A)) 
      opCl : ((ClLeftBiMagmaTerm A) → ((ClLeftBiMagmaTerm A) → (ClLeftBiMagmaTerm A))) 
      linvCl : ((ClLeftBiMagmaTerm A) → ((ClLeftBiMagmaTerm A) → (ClLeftBiMagmaTerm A)))  
      
  data OpLeftBiMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftBiMagmaTerm n)) 
      opOL : ((OpLeftBiMagmaTerm n) → ((OpLeftBiMagmaTerm n) → (OpLeftBiMagmaTerm n))) 
      linvOL : ((OpLeftBiMagmaTerm n) → ((OpLeftBiMagmaTerm n) → (OpLeftBiMagmaTerm n)))  
      
  data OpLeftBiMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftBiMagmaTerm2 n A)) 
      sing2 : (A → (OpLeftBiMagmaTerm2 n A)) 
      opOL2 : ((OpLeftBiMagmaTerm2 n A) → ((OpLeftBiMagmaTerm2 n A) → (OpLeftBiMagmaTerm2 n A))) 
      linvOL2 : ((OpLeftBiMagmaTerm2 n A) → ((OpLeftBiMagmaTerm2 n A) → (OpLeftBiMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClLeftBiMagmaTerm A) → (ClLeftBiMagmaTerm A)) 
  simplifyCl _ (opCl x1 x2) = (opCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (linvCl x1 x2) = (linvCl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpLeftBiMagmaTerm n) → (OpLeftBiMagmaTerm n)) 
  simplifyOpB _ (opOL x1 x2) = (opOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (linvOL x1 x2) = (linvOL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpLeftBiMagmaTerm2 n A) → (OpLeftBiMagmaTerm2 n A)) 
  simplifyOp _ _ (opOL2 x1 x2) = (opOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (linvOL2 x1 x2) = (linvOL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftBiMagma A) → (LeftBiMagmaTerm → A)) 
  evalB Le (opL x1 x2) = ((op Le) (evalB Le x1) (evalB Le x2))  
  evalB Le (linvL x1 x2) = ((linv Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftBiMagma A) → ((ClLeftBiMagmaTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (opCl x1 x2) = ((op Le) (evalCl Le x1) (evalCl Le x2))  
  evalCl Le (linvCl x1 x2) = ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((LeftBiMagma A) → ((Vec A n) → ((OpLeftBiMagmaTerm n) → A))) 
  evalOpB n Le vars (v x1) = (lookup vars x1)  
  evalOpB n Le vars (opOL x1 x2) = ((op Le) (evalOpB n Le vars x1) (evalOpB n Le vars x2))  
  evalOpB n Le vars (linvOL x1 x2) = ((linv Le) (evalOpB n Le vars x1) (evalOpB n Le vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((LeftBiMagma A) → ((Vec A n) → ((OpLeftBiMagmaTerm2 n A) → A))) 
  evalOp n Le vars (v2 x1) = (lookup vars x1)  
  evalOp n Le vars (sing2 x1) = x1  
  evalOp n Le vars (opOL2 x1 x2) = ((op Le) (evalOp n Le vars x1) (evalOp n Le vars x2))  
  evalOp n Le vars (linvOL2 x1 x2) = ((linv Le) (evalOp n Le vars x1) (evalOp n Le vars x2))  
  inductionB :  (P : (LeftBiMagmaTerm → Set)) →  (( (x1 x2 : LeftBiMagmaTerm) → ((P x1) → ((P x2) → (P (opL x1 x2))))) → (( (x1 x2 : LeftBiMagmaTerm) → ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ( (x : LeftBiMagmaTerm) → (P x)))) 
  inductionB p popl plinvl (opL x1 x2) = (popl _ _ (inductionB p popl plinvl x1) (inductionB p popl plinvl x2))  
  inductionB p popl plinvl (linvL x1 x2) = (plinvl _ _ (inductionB p popl plinvl x1) (inductionB p popl plinvl x2))  
  inductionCl :  (A : Set) (P : ((ClLeftBiMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftBiMagmaTerm A)) → ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (( (x1 x2 : (ClLeftBiMagmaTerm A)) → ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ( (x : (ClLeftBiMagmaTerm A)) → (P x))))) 
  inductionCl _ p psing popcl plinvcl (sing x1) = (psing x1)  
  inductionCl _ p psing popcl plinvcl (opCl x1 x2) = (popcl _ _ (inductionCl _ p psing popcl plinvcl x1) (inductionCl _ p psing popcl plinvcl x2))  
  inductionCl _ p psing popcl plinvcl (linvCl x1 x2) = (plinvcl _ _ (inductionCl _ p psing popcl plinvcl x1) (inductionCl _ p psing popcl plinvcl x2))  
  inductionOpB :  (n : Nat) (P : ((OpLeftBiMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftBiMagmaTerm n)) → ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (( (x1 x2 : (OpLeftBiMagmaTerm n)) → ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ( (x : (OpLeftBiMagmaTerm n)) → (P x))))) 
  inductionOpB _ p pv popol plinvol (v x1) = (pv x1)  
  inductionOpB _ p pv popol plinvol (opOL x1 x2) = (popol _ _ (inductionOpB _ p pv popol plinvol x1) (inductionOpB _ p pv popol plinvol x2))  
  inductionOpB _ p pv popol plinvol (linvOL x1 x2) = (plinvol _ _ (inductionOpB _ p pv popol plinvol x1) (inductionOpB _ p pv popol plinvol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpLeftBiMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftBiMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (( (x1 x2 : (OpLeftBiMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ( (x : (OpLeftBiMagmaTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 (opOL2 x1 x2) = (popol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 plinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 plinvol2 x2))  
  inductionOp _ _ p pv2 psing2 popol2 plinvol2 (linvOL2 x1 x2) = (plinvol2 _ _ (inductionOp _ _ p pv2 psing2 popol2 plinvol2 x1) (inductionOp _ _ p pv2 psing2 popol2 plinvol2 x2))  
  stageB :  (LeftBiMagmaTerm → (Staged LeftBiMagmaTerm))
  stageB (opL x1 x2) = (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  stageB (linvL x1 x2) = (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClLeftBiMagmaTerm A) → (Staged (ClLeftBiMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (opCl x1 x2) = (stage2 opCl (codeLift2 opCl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (linvCl x1 x2) = (stage2 linvCl (codeLift2 linvCl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpLeftBiMagmaTerm n) → (Staged (OpLeftBiMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (opOL x1 x2) = (stage2 opOL (codeLift2 opOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (linvOL x1 x2) = (stage2 linvOL (codeLift2 linvOL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpLeftBiMagmaTerm2 n A) → (Staged (OpLeftBiMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (opOL2 x1 x2) = (stage2 opOL2 (codeLift2 opOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (linvOL2 x1 x2) = (stage2 linvOL2 (codeLift2 linvOL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      opT : ((Repr A) → ((Repr A) → (Repr A))) 
      linvT : ((Repr A) → ((Repr A) → (Repr A)))  
  
 