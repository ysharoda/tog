import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightSpindle_Shelf   
  structure RightSpindle_Shelf  (A : Type) : Type := 
       (rinv : (A → (A → A)))
       (rightDistributive : (∀ {x y z : A} , (rinv (rinv y z) x) = (rinv (rinv y x) (rinv z x))))
       (idempotent_rinv : (∀ {x : A} , (rinv x x) = x))
       (linv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z)))) 
  
  open RightSpindle_Shelf
  structure Sig  (AS : Type) : Type := 
       (rinvS : (AS → (AS → AS)))
       (linvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightDistributiveP : (∀ {xP yP zP : (Prod A A)} , (rinvP (rinvP yP zP) xP) = (rinvP (rinvP yP xP) (rinvP zP xP))))
       (idempotent_rinvP : (∀ {xP : (Prod A A)} , (rinvP xP xP) = xP))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightSpindle_Shelf A1)) (Ri2 : (RightSpindle_Shelf A2)) : Type := 
       (hom : (A1 → A2))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Ri1) x1 x2)) = ((rinv Ri2) (hom x1) (hom x2))))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Ri1) x1 x2)) = ((linv Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightSpindle_Shelf A1)) (Ri2 : (RightSpindle_Shelf A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2))))))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Ri1) x1 x2) ((linv Ri2) y1 y2)))))) 
  
  inductive RightSpindle_ShelfTerm   : Type  
     | rinvL : (RightSpindle_ShelfTerm → (RightSpindle_ShelfTerm → RightSpindle_ShelfTerm)) 
     | linvL : (RightSpindle_ShelfTerm → (RightSpindle_ShelfTerm → RightSpindle_ShelfTerm))  
      open RightSpindle_ShelfTerm 
  
  inductive ClRightSpindle_ShelfTerm  (A : Type) : Type  
     | sing : (A → ClRightSpindle_ShelfTerm) 
     | rinvCl : (ClRightSpindle_ShelfTerm → (ClRightSpindle_ShelfTerm → ClRightSpindle_ShelfTerm)) 
     | linvCl : (ClRightSpindle_ShelfTerm → (ClRightSpindle_ShelfTerm → ClRightSpindle_ShelfTerm))  
      open ClRightSpindle_ShelfTerm 
  
  inductive OpRightSpindle_ShelfTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightSpindle_ShelfTerm) 
     | rinvOL : (OpRightSpindle_ShelfTerm → (OpRightSpindle_ShelfTerm → OpRightSpindle_ShelfTerm)) 
     | linvOL : (OpRightSpindle_ShelfTerm → (OpRightSpindle_ShelfTerm → OpRightSpindle_ShelfTerm))  
      open OpRightSpindle_ShelfTerm 
  
  inductive OpRightSpindle_ShelfTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightSpindle_ShelfTerm2) 
     | sing2 : (A → OpRightSpindle_ShelfTerm2) 
     | rinvOL2 : (OpRightSpindle_ShelfTerm2 → (OpRightSpindle_ShelfTerm2 → OpRightSpindle_ShelfTerm2)) 
     | linvOL2 : (OpRightSpindle_ShelfTerm2 → (OpRightSpindle_ShelfTerm2 → OpRightSpindle_ShelfTerm2))  
      open OpRightSpindle_ShelfTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightSpindle_ShelfTerm A) → (ClRightSpindle_ShelfTerm A)) 
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightSpindle_ShelfTerm n) → (OpRightSpindle_ShelfTerm n)) 
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightSpindle_ShelfTerm2 n A) → (OpRightSpindle_ShelfTerm2 n A)) 
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightSpindle_Shelf A) → (RightSpindle_ShelfTerm → A)) 
  | Ri (rinvL x1 x2) := ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (linvL x1 x2) := ((linv Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightSpindle_Shelf A) → ((ClRightSpindle_ShelfTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (rinvCl x1 x2) := ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (linvCl x1 x2) := ((linv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightSpindle_Shelf A) → ((vector A n) → ((OpRightSpindle_ShelfTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (rinvOL x1 x2) := ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (linvOL x1 x2) := ((linv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightSpindle_Shelf A) → ((vector A n) → ((OpRightSpindle_ShelfTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (rinvOL2 x1 x2) := ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (linvOL2 x1 x2) := ((linv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightSpindle_ShelfTerm → Type)}  : ((∀ (x1 x2 : RightSpindle_ShelfTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → ((∀ (x1 x2 : RightSpindle_ShelfTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (∀ (x : RightSpindle_ShelfTerm) , (P x)))) 
  | prinvl plinvl (rinvL x1 x2) := (prinvl _ _ (inductionB prinvl plinvl x1) (inductionB prinvl plinvl x2))  
  | prinvl plinvl (linvL x1 x2) := (plinvl _ _ (inductionB prinvl plinvl x1) (inductionB prinvl plinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRightSpindle_ShelfTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightSpindle_ShelfTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → ((∀ (x1 x2 : (ClRightSpindle_ShelfTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (∀ (x : (ClRightSpindle_ShelfTerm A)) , (P x))))) 
  | psing prinvcl plinvcl (sing x1) := (psing x1)  
  | psing prinvcl plinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing prinvcl plinvcl x1) (inductionCl psing prinvcl plinvcl x2))  
  | psing prinvcl plinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing prinvcl plinvcl x1) (inductionCl psing prinvcl plinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightSpindle_ShelfTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightSpindle_ShelfTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → ((∀ (x1 x2 : (OpRightSpindle_ShelfTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (∀ (x : (OpRightSpindle_ShelfTerm n)) , (P x))))) 
  | pv prinvol plinvol (v x1) := (pv x1)  
  | pv prinvol plinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv prinvol plinvol x1) (inductionOpB pv prinvol plinvol x2))  
  | pv prinvol plinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv prinvol plinvol x1) (inductionOpB pv prinvol plinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightSpindle_ShelfTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightSpindle_ShelfTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRightSpindle_ShelfTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (∀ (x : (OpRightSpindle_ShelfTerm2 n A)) , (P x)))))) 
  | pv2 psing2 prinvol2 plinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 prinvol2 plinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 prinvol2 plinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 prinvol2 plinvol2 x1) (inductionOp pv2 psing2 prinvol2 plinvol2 x2))  
  | pv2 psing2 prinvol2 plinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 prinvol2 plinvol2 x1) (inductionOp pv2 psing2 prinvol2 plinvol2 x2))  
  def stageB  : (RightSpindle_ShelfTerm → (Staged RightSpindle_ShelfTerm))
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightSpindle_ShelfTerm A) → (Staged (ClRightSpindle_ShelfTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightSpindle_ShelfTerm n) → (Staged (OpRightSpindle_ShelfTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightSpindle_ShelfTerm2 n A) → (Staged (OpRightSpindle_ShelfTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (rinvT : ((Repr A) → ((Repr A) → (Repr A))))
       (linvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightSpindle_Shelf