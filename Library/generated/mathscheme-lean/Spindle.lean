import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Spindle   
  structure Spindle  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z))))
       (rightDistributive : (∀ {x y z : A} , (rinv (rinv y z) x) = (rinv (rinv y x) (rinv z x))))
       (idempotent_linv : (∀ {x : A} , (linv x x) = x))
       (idempotent_rinv : (∀ {x : A} , (rinv x x) = x)) 
  
  open Spindle
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP))))
       (rightDistributiveP : (∀ {xP yP zP : (Prod A A)} , (rinvP (rinvP yP zP) xP) = (rinvP (rinvP yP xP) (rinvP zP xP))))
       (idempotent_linvP : (∀ {xP : (Prod A A)} , (linvP xP xP) = xP))
       (idempotent_rinvP : (∀ {xP : (Prod A A)} , (rinvP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Sp1 : (Spindle A1)) (Sp2 : (Spindle A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Sp1) x1 x2)) = ((linv Sp2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Sp1) x1 x2)) = ((rinv Sp2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Sp1 : (Spindle A1)) (Sp2 : (Spindle A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Sp1) x1 x2) ((linv Sp2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Sp1) x1 x2) ((rinv Sp2) y1 y2)))))) 
  
  inductive SpindleTerm   : Type  
     | linvL : (SpindleTerm → (SpindleTerm → SpindleTerm)) 
     | rinvL : (SpindleTerm → (SpindleTerm → SpindleTerm))  
      open SpindleTerm 
  
  inductive ClSpindleTerm  (A : Type) : Type  
     | sing : (A → ClSpindleTerm) 
     | linvCl : (ClSpindleTerm → (ClSpindleTerm → ClSpindleTerm)) 
     | rinvCl : (ClSpindleTerm → (ClSpindleTerm → ClSpindleTerm))  
      open ClSpindleTerm 
  
  inductive OpSpindleTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSpindleTerm) 
     | linvOL : (OpSpindleTerm → (OpSpindleTerm → OpSpindleTerm)) 
     | rinvOL : (OpSpindleTerm → (OpSpindleTerm → OpSpindleTerm))  
      open OpSpindleTerm 
  
  inductive OpSpindleTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSpindleTerm2) 
     | sing2 : (A → OpSpindleTerm2) 
     | linvOL2 : (OpSpindleTerm2 → (OpSpindleTerm2 → OpSpindleTerm2)) 
     | rinvOL2 : (OpSpindleTerm2 → (OpSpindleTerm2 → OpSpindleTerm2))  
      open OpSpindleTerm2 
  
  def simplifyCl   {A : Type}  : ((ClSpindleTerm A) → (ClSpindleTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpSpindleTerm n) → (OpSpindleTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpSpindleTerm2 n A) → (OpSpindleTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Spindle A) → (SpindleTerm → A)) 
  | Sp (linvL x1 x2) := ((linv Sp) (evalB Sp x1) (evalB Sp x2))  
  | Sp (rinvL x1 x2) := ((rinv Sp) (evalB Sp x1) (evalB Sp x2))  
  def evalCl   {A : Type}  : ((Spindle A) → ((ClSpindleTerm A) → A)) 
  | Sp (sing x1) := x1  
  | Sp (linvCl x1 x2) := ((linv Sp) (evalCl Sp x1) (evalCl Sp x2))  
  | Sp (rinvCl x1 x2) := ((rinv Sp) (evalCl Sp x1) (evalCl Sp x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Spindle A) → ((vector A n) → ((OpSpindleTerm n) → A))) 
  | Sp vars (v x1) := (nth vars x1)  
  | Sp vars (linvOL x1 x2) := ((linv Sp) (evalOpB Sp vars x1) (evalOpB Sp vars x2))  
  | Sp vars (rinvOL x1 x2) := ((rinv Sp) (evalOpB Sp vars x1) (evalOpB Sp vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Spindle A) → ((vector A n) → ((OpSpindleTerm2 n A) → A))) 
  | Sp vars (v2 x1) := (nth vars x1)  
  | Sp vars (sing2 x1) := x1  
  | Sp vars (linvOL2 x1 x2) := ((linv Sp) (evalOp Sp vars x1) (evalOp Sp vars x2))  
  | Sp vars (rinvOL2 x1 x2) := ((rinv Sp) (evalOp Sp vars x1) (evalOp Sp vars x2))  
  def inductionB   {P : (SpindleTerm → Type)}  : ((∀ (x1 x2 : SpindleTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : SpindleTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : SpindleTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClSpindleTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClSpindleTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClSpindleTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClSpindleTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpSpindleTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpSpindleTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpSpindleTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpSpindleTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpSpindleTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpSpindleTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpSpindleTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpSpindleTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (SpindleTerm → (Staged SpindleTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClSpindleTerm A) → (Staged (ClSpindleTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpSpindleTerm n) → (Staged (OpSpindleTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpSpindleTerm2 n A) → (Staged (OpSpindleTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Spindle