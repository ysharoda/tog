import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MedialQuasiGroup   
  structure MedialQuasiGroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (linv : (A → (A → A)))
       (leftCancel : (∀ {x y : A} , (op x (linv x y)) = y))
       (lefCancelOp : (∀ {x y : A} , (linv x (op x y)) = y))
       (rinv : (A → (A → A)))
       (rightCancel : (∀ {x y : A} , (op (rinv y x) x) = y))
       (rightCancelOp : (∀ {x y : A} , (rinv (op y x) x) = y))
       (mediates : (∀ {w x y z : A} , (op (op x y) (op z w)) = (op (op x z) (op y w)))) 
  
  open MedialQuasiGroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftCancelP : (∀ {xP yP : (Prod A A)} , (opP xP (linvP xP yP)) = yP))
       (lefCancelOpP : (∀ {xP yP : (Prod A A)} , (linvP xP (opP xP yP)) = yP))
       (rightCancelP : (∀ {xP yP : (Prod A A)} , (opP (rinvP yP xP) xP) = yP))
       (rightCancelOpP : (∀ {xP yP : (Prod A A)} , (rinvP (opP yP xP) xP) = yP))
       (mediatesP : (∀ {wP xP yP zP : (Prod A A)} , (opP (opP xP yP) (opP zP wP)) = (opP (opP xP zP) (opP yP wP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Me1 : (MedialQuasiGroup A1)) (Me2 : (MedialQuasiGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Me1) x1 x2)) = ((op Me2) (hom x1) (hom x2))))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Me1) x1 x2)) = ((linv Me2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Me1) x1 x2)) = ((rinv Me2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Me1 : (MedialQuasiGroup A1)) (Me2 : (MedialQuasiGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Me1) x1 x2) ((op Me2) y1 y2))))))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Me1) x1 x2) ((linv Me2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Me1) x1 x2) ((rinv Me2) y1 y2)))))) 
  
  inductive MedialQuasiGroupTerm   : Type  
     | opL : (MedialQuasiGroupTerm → (MedialQuasiGroupTerm → MedialQuasiGroupTerm)) 
     | linvL : (MedialQuasiGroupTerm → (MedialQuasiGroupTerm → MedialQuasiGroupTerm)) 
     | rinvL : (MedialQuasiGroupTerm → (MedialQuasiGroupTerm → MedialQuasiGroupTerm))  
      open MedialQuasiGroupTerm 
  
  inductive ClMedialQuasiGroupTerm  (A : Type) : Type  
     | sing : (A → ClMedialQuasiGroupTerm) 
     | opCl : (ClMedialQuasiGroupTerm → (ClMedialQuasiGroupTerm → ClMedialQuasiGroupTerm)) 
     | linvCl : (ClMedialQuasiGroupTerm → (ClMedialQuasiGroupTerm → ClMedialQuasiGroupTerm)) 
     | rinvCl : (ClMedialQuasiGroupTerm → (ClMedialQuasiGroupTerm → ClMedialQuasiGroupTerm))  
      open ClMedialQuasiGroupTerm 
  
  inductive OpMedialQuasiGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMedialQuasiGroupTerm) 
     | opOL : (OpMedialQuasiGroupTerm → (OpMedialQuasiGroupTerm → OpMedialQuasiGroupTerm)) 
     | linvOL : (OpMedialQuasiGroupTerm → (OpMedialQuasiGroupTerm → OpMedialQuasiGroupTerm)) 
     | rinvOL : (OpMedialQuasiGroupTerm → (OpMedialQuasiGroupTerm → OpMedialQuasiGroupTerm))  
      open OpMedialQuasiGroupTerm 
  
  inductive OpMedialQuasiGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMedialQuasiGroupTerm2) 
     | sing2 : (A → OpMedialQuasiGroupTerm2) 
     | opOL2 : (OpMedialQuasiGroupTerm2 → (OpMedialQuasiGroupTerm2 → OpMedialQuasiGroupTerm2)) 
     | linvOL2 : (OpMedialQuasiGroupTerm2 → (OpMedialQuasiGroupTerm2 → OpMedialQuasiGroupTerm2)) 
     | rinvOL2 : (OpMedialQuasiGroupTerm2 → (OpMedialQuasiGroupTerm2 → OpMedialQuasiGroupTerm2))  
      open OpMedialQuasiGroupTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMedialQuasiGroupTerm A) → (ClMedialQuasiGroupTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMedialQuasiGroupTerm n) → (OpMedialQuasiGroupTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMedialQuasiGroupTerm2 n A) → (OpMedialQuasiGroupTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MedialQuasiGroup A) → (MedialQuasiGroupTerm → A)) 
  | Me (opL x1 x2) := ((op Me) (evalB Me x1) (evalB Me x2))  
  | Me (linvL x1 x2) := ((linv Me) (evalB Me x1) (evalB Me x2))  
  | Me (rinvL x1 x2) := ((rinv Me) (evalB Me x1) (evalB Me x2))  
  def evalCl   {A : Type}  : ((MedialQuasiGroup A) → ((ClMedialQuasiGroupTerm A) → A)) 
  | Me (sing x1) := x1  
  | Me (opCl x1 x2) := ((op Me) (evalCl Me x1) (evalCl Me x2))  
  | Me (linvCl x1 x2) := ((linv Me) (evalCl Me x1) (evalCl Me x2))  
  | Me (rinvCl x1 x2) := ((rinv Me) (evalCl Me x1) (evalCl Me x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((MedialQuasiGroup A) → ((vector A n) → ((OpMedialQuasiGroupTerm n) → A))) 
  | Me vars (v x1) := (nth vars x1)  
  | Me vars (opOL x1 x2) := ((op Me) (evalOpB Me vars x1) (evalOpB Me vars x2))  
  | Me vars (linvOL x1 x2) := ((linv Me) (evalOpB Me vars x1) (evalOpB Me vars x2))  
  | Me vars (rinvOL x1 x2) := ((rinv Me) (evalOpB Me vars x1) (evalOpB Me vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((MedialQuasiGroup A) → ((vector A n) → ((OpMedialQuasiGroupTerm2 n A) → A))) 
  | Me vars (v2 x1) := (nth vars x1)  
  | Me vars (sing2 x1) := x1  
  | Me vars (opOL2 x1 x2) := ((op Me) (evalOp Me vars x1) (evalOp Me vars x2))  
  | Me vars (linvOL2 x1 x2) := ((linv Me) (evalOp Me vars x1) (evalOp Me vars x2))  
  | Me vars (rinvOL2 x1 x2) := ((rinv Me) (evalOp Me vars x1) (evalOp Me vars x2))  
  def inductionB   {P : (MedialQuasiGroupTerm → Type)}  : ((∀ (x1 x2 : MedialQuasiGroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((∀ (x1 x2 : MedialQuasiGroupTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : MedialQuasiGroupTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : MedialQuasiGroupTerm) , (P x))))) 
  | popl plinvl prinvl (opL x1 x2) := (popl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  | popl plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  | popl plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClMedialQuasiGroupTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMedialQuasiGroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((∀ (x1 x2 : (ClMedialQuasiGroupTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClMedialQuasiGroupTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClMedialQuasiGroupTerm A)) , (P x)))))) 
  | psing popcl plinvcl prinvcl (sing x1) := (psing x1)  
  | psing popcl plinvcl prinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  | psing popcl plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  | psing popcl plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMedialQuasiGroupTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMedialQuasiGroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((∀ (x1 x2 : (OpMedialQuasiGroupTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpMedialQuasiGroupTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpMedialQuasiGroupTerm n)) , (P x)))))) 
  | pv popol plinvol prinvol (v x1) := (pv x1)  
  | pv popol plinvol prinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  | pv popol plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  | pv popol plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMedialQuasiGroupTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMedialQuasiGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((∀ (x1 x2 : (OpMedialQuasiGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpMedialQuasiGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpMedialQuasiGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  | pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  | pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  def stageB  : (MedialQuasiGroupTerm → (Staged MedialQuasiGroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMedialQuasiGroupTerm A) → (Staged (ClMedialQuasiGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMedialQuasiGroupTerm n) → (Staged (OpMedialQuasiGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMedialQuasiGroupTerm2 n A) → (Staged (OpMedialQuasiGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MedialQuasiGroup