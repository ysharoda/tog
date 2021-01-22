import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightSpindle   
  structure RightSpindle  (A : Type) : Type := 
       (rinv : (A → (A → A)))
       (rightDistributive : (∀ {x y z : A} , (rinv (rinv y z) x) = (rinv (rinv y x) (rinv z x))))
       (idempotent_rinv : (∀ {x : A} , (rinv x x) = x)) 
  
  open RightSpindle
  structure Sig  (AS : Type) : Type := 
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightDistributiveP : (∀ {xP yP zP : (Prod A A)} , (rinvP (rinvP yP zP) xP) = (rinvP (rinvP yP xP) (rinvP zP xP))))
       (idempotent_rinvP : (∀ {xP : (Prod A A)} , (rinvP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightSpindle A1)) (Ri2 : (RightSpindle A2)) : Type := 
       (hom : (A1 → A2))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Ri1) x1 x2)) = ((rinv Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightSpindle A1)) (Ri2 : (RightSpindle A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))) 
  
  inductive RightSpindleTerm   : Type  
     | rinvL : (RightSpindleTerm → (RightSpindleTerm → RightSpindleTerm))  
      open RightSpindleTerm 
  
  inductive ClRightSpindleTerm  (A : Type) : Type  
     | sing : (A → ClRightSpindleTerm) 
     | rinvCl : (ClRightSpindleTerm → (ClRightSpindleTerm → ClRightSpindleTerm))  
      open ClRightSpindleTerm 
  
  inductive OpRightSpindleTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightSpindleTerm) 
     | rinvOL : (OpRightSpindleTerm → (OpRightSpindleTerm → OpRightSpindleTerm))  
      open OpRightSpindleTerm 
  
  inductive OpRightSpindleTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightSpindleTerm2) 
     | sing2 : (A → OpRightSpindleTerm2) 
     | rinvOL2 : (OpRightSpindleTerm2 → (OpRightSpindleTerm2 → OpRightSpindleTerm2))  
      open OpRightSpindleTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightSpindleTerm A) → (ClRightSpindleTerm A)) 
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightSpindleTerm n) → (OpRightSpindleTerm n)) 
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightSpindleTerm2 n A) → (OpRightSpindleTerm2 n A)) 
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightSpindle A) → (RightSpindleTerm → A)) 
  | Ri (rinvL x1 x2) := ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightSpindle A) → ((ClRightSpindleTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (rinvCl x1 x2) := ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightSpindle A) → ((vector A n) → ((OpRightSpindleTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (rinvOL x1 x2) := ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightSpindle A) → ((vector A n) → ((OpRightSpindleTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (rinvOL2 x1 x2) := ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightSpindleTerm → Type)}  : ((∀ (x1 x2 : RightSpindleTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : RightSpindleTerm) , (P x))) 
  | prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB prinvl x1) (inductionB prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRightSpindleTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightSpindleTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClRightSpindleTerm A)) , (P x)))) 
  | psing prinvcl (sing x1) := (psing x1)  
  | psing prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing prinvcl x1) (inductionCl psing prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightSpindleTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightSpindleTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpRightSpindleTerm n)) , (P x)))) 
  | pv prinvol (v x1) := (pv x1)  
  | pv prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv prinvol x1) (inductionOpB pv prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightSpindleTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightSpindleTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpRightSpindleTerm2 n A)) , (P x))))) 
  | pv2 psing2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 prinvol2 x1) (inductionOp pv2 psing2 prinvol2 x2))  
  def stageB  : (RightSpindleTerm → (Staged RightSpindleTerm))
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightSpindleTerm A) → (Staged (ClRightSpindleTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightSpindleTerm n) → (Staged (OpRightSpindleTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightSpindleTerm2 n A) → (Staged (OpRightSpindleTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightSpindle