import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightBiMagma   
  structure RightBiMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (rinv : (A → (A → A))) 
  
  open RightBiMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightBiMagma A1)) (Ri2 : (RightBiMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ri1) x1 x2)) = ((op Ri2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Ri1) x1 x2)) = ((rinv Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightBiMagma A1)) (Ri2 : (RightBiMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))) 
  
  inductive RightBiMagmaTerm   : Type  
     | opL : (RightBiMagmaTerm → (RightBiMagmaTerm → RightBiMagmaTerm)) 
     | rinvL : (RightBiMagmaTerm → (RightBiMagmaTerm → RightBiMagmaTerm))  
      open RightBiMagmaTerm 
  
  inductive ClRightBiMagmaTerm  (A : Type) : Type  
     | sing : (A → ClRightBiMagmaTerm) 
     | opCl : (ClRightBiMagmaTerm → (ClRightBiMagmaTerm → ClRightBiMagmaTerm)) 
     | rinvCl : (ClRightBiMagmaTerm → (ClRightBiMagmaTerm → ClRightBiMagmaTerm))  
      open ClRightBiMagmaTerm 
  
  inductive OpRightBiMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightBiMagmaTerm) 
     | opOL : (OpRightBiMagmaTerm → (OpRightBiMagmaTerm → OpRightBiMagmaTerm)) 
     | rinvOL : (OpRightBiMagmaTerm → (OpRightBiMagmaTerm → OpRightBiMagmaTerm))  
      open OpRightBiMagmaTerm 
  
  inductive OpRightBiMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightBiMagmaTerm2) 
     | sing2 : (A → OpRightBiMagmaTerm2) 
     | opOL2 : (OpRightBiMagmaTerm2 → (OpRightBiMagmaTerm2 → OpRightBiMagmaTerm2)) 
     | rinvOL2 : (OpRightBiMagmaTerm2 → (OpRightBiMagmaTerm2 → OpRightBiMagmaTerm2))  
      open OpRightBiMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightBiMagmaTerm A) → (ClRightBiMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightBiMagmaTerm n) → (OpRightBiMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightBiMagmaTerm2 n A) → (OpRightBiMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightBiMagma A) → (RightBiMagmaTerm → A)) 
  | Ri (opL x1 x2) := ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (rinvL x1 x2) := ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightBiMagma A) → ((ClRightBiMagmaTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (opCl x1 x2) := ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (rinvCl x1 x2) := ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightBiMagma A) → ((vector A n) → ((OpRightBiMagmaTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (opOL x1 x2) := ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (rinvOL x1 x2) := ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightBiMagma A) → ((vector A n) → ((OpRightBiMagmaTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (opOL2 x1 x2) := ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (rinvOL2 x1 x2) := ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightBiMagmaTerm → Type)}  : ((∀ (x1 x2 : RightBiMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((∀ (x1 x2 : RightBiMagmaTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : RightBiMagmaTerm) , (P x)))) 
  | popl prinvl (opL x1 x2) := (popl _ _ (inductionB popl prinvl x1) (inductionB popl prinvl x2))  
  | popl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB popl prinvl x1) (inductionB popl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRightBiMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightBiMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((∀ (x1 x2 : (ClRightBiMagmaTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClRightBiMagmaTerm A)) , (P x))))) 
  | psing popcl prinvcl (sing x1) := (psing x1)  
  | psing popcl prinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl prinvcl x1) (inductionCl psing popcl prinvcl x2))  
  | psing popcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing popcl prinvcl x1) (inductionCl psing popcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightBiMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightBiMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((∀ (x1 x2 : (OpRightBiMagmaTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpRightBiMagmaTerm n)) , (P x))))) 
  | pv popol prinvol (v x1) := (pv x1)  
  | pv popol prinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol prinvol x1) (inductionOpB pv popol prinvol x2))  
  | pv popol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv popol prinvol x1) (inductionOpB pv popol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightBiMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightBiMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRightBiMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpRightBiMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 prinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 prinvol2 x2))  
  | pv2 psing2 popol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 popol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 prinvol2 x2))  
  def stageB  : (RightBiMagmaTerm → (Staged RightBiMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightBiMagmaTerm A) → (Staged (ClRightBiMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightBiMagmaTerm n) → (Staged (OpRightBiMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightBiMagmaTerm2 n A) → (Staged (OpRightBiMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightBiMagma