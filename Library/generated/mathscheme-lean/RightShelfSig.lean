import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightShelfSig   
  structure RightShelfSig  (A : Type) : Type := 
       (rinv : (A → (A → A))) 
  
  open RightShelfSig
  structure Sig  (AS : Type) : Type := 
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightShelfSig A1)) (Ri2 : (RightShelfSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Ri1) x1 x2)) = ((rinv Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightShelfSig A1)) (Ri2 : (RightShelfSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))) 
  
  inductive RightShelfSigTerm   : Type  
     | rinvL : (RightShelfSigTerm → (RightShelfSigTerm → RightShelfSigTerm))  
      open RightShelfSigTerm 
  
  inductive ClRightShelfSigTerm  (A : Type) : Type  
     | sing : (A → ClRightShelfSigTerm) 
     | rinvCl : (ClRightShelfSigTerm → (ClRightShelfSigTerm → ClRightShelfSigTerm))  
      open ClRightShelfSigTerm 
  
  inductive OpRightShelfSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightShelfSigTerm) 
     | rinvOL : (OpRightShelfSigTerm → (OpRightShelfSigTerm → OpRightShelfSigTerm))  
      open OpRightShelfSigTerm 
  
  inductive OpRightShelfSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightShelfSigTerm2) 
     | sing2 : (A → OpRightShelfSigTerm2) 
     | rinvOL2 : (OpRightShelfSigTerm2 → (OpRightShelfSigTerm2 → OpRightShelfSigTerm2))  
      open OpRightShelfSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightShelfSigTerm A) → (ClRightShelfSigTerm A)) 
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightShelfSigTerm n) → (OpRightShelfSigTerm n)) 
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightShelfSigTerm2 n A) → (OpRightShelfSigTerm2 n A)) 
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightShelfSig A) → (RightShelfSigTerm → A)) 
  | Ri (rinvL x1 x2) := ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightShelfSig A) → ((ClRightShelfSigTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (rinvCl x1 x2) := ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightShelfSig A) → ((vector A n) → ((OpRightShelfSigTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (rinvOL x1 x2) := ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightShelfSig A) → ((vector A n) → ((OpRightShelfSigTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (rinvOL2 x1 x2) := ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightShelfSigTerm → Type)}  : ((∀ (x1 x2 : RightShelfSigTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : RightShelfSigTerm) , (P x))) 
  | prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB prinvl x1) (inductionB prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRightShelfSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightShelfSigTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClRightShelfSigTerm A)) , (P x)))) 
  | psing prinvcl (sing x1) := (psing x1)  
  | psing prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing prinvcl x1) (inductionCl psing prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightShelfSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightShelfSigTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpRightShelfSigTerm n)) , (P x)))) 
  | pv prinvol (v x1) := (pv x1)  
  | pv prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv prinvol x1) (inductionOpB pv prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightShelfSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightShelfSigTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpRightShelfSigTerm2 n A)) , (P x))))) 
  | pv2 psing2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 prinvol2 x1) (inductionOp pv2 psing2 prinvol2 x2))  
  def stageB  : (RightShelfSigTerm → (Staged RightShelfSigTerm))
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightShelfSigTerm A) → (Staged (ClRightShelfSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightShelfSigTerm n) → (Staged (OpRightShelfSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightShelfSigTerm2 n A) → (Staged (OpRightShelfSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightShelfSig