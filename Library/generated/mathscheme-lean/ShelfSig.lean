import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section ShelfSig   
  structure ShelfSig  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A))) 
  
  open ShelfSig
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Sh1 : (ShelfSig A1)) (Sh2 : (ShelfSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Sh1) x1 x2)) = ((linv Sh2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Sh1) x1 x2)) = ((rinv Sh2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Sh1 : (ShelfSig A1)) (Sh2 : (ShelfSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Sh1) x1 x2) ((linv Sh2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Sh1) x1 x2) ((rinv Sh2) y1 y2)))))) 
  
  inductive ShelfSigTerm   : Type  
     | linvL : (ShelfSigTerm → (ShelfSigTerm → ShelfSigTerm)) 
     | rinvL : (ShelfSigTerm → (ShelfSigTerm → ShelfSigTerm))  
      open ShelfSigTerm 
  
  inductive ClShelfSigTerm  (A : Type) : Type  
     | sing : (A → ClShelfSigTerm) 
     | linvCl : (ClShelfSigTerm → (ClShelfSigTerm → ClShelfSigTerm)) 
     | rinvCl : (ClShelfSigTerm → (ClShelfSigTerm → ClShelfSigTerm))  
      open ClShelfSigTerm 
  
  inductive OpShelfSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpShelfSigTerm) 
     | linvOL : (OpShelfSigTerm → (OpShelfSigTerm → OpShelfSigTerm)) 
     | rinvOL : (OpShelfSigTerm → (OpShelfSigTerm → OpShelfSigTerm))  
      open OpShelfSigTerm 
  
  inductive OpShelfSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpShelfSigTerm2) 
     | sing2 : (A → OpShelfSigTerm2) 
     | linvOL2 : (OpShelfSigTerm2 → (OpShelfSigTerm2 → OpShelfSigTerm2)) 
     | rinvOL2 : (OpShelfSigTerm2 → (OpShelfSigTerm2 → OpShelfSigTerm2))  
      open OpShelfSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClShelfSigTerm A) → (ClShelfSigTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpShelfSigTerm n) → (OpShelfSigTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpShelfSigTerm2 n A) → (OpShelfSigTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((ShelfSig A) → (ShelfSigTerm → A)) 
  | Sh (linvL x1 x2) := ((linv Sh) (evalB Sh x1) (evalB Sh x2))  
  | Sh (rinvL x1 x2) := ((rinv Sh) (evalB Sh x1) (evalB Sh x2))  
  def evalCl   {A : Type}  : ((ShelfSig A) → ((ClShelfSigTerm A) → A)) 
  | Sh (sing x1) := x1  
  | Sh (linvCl x1 x2) := ((linv Sh) (evalCl Sh x1) (evalCl Sh x2))  
  | Sh (rinvCl x1 x2) := ((rinv Sh) (evalCl Sh x1) (evalCl Sh x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((ShelfSig A) → ((vector A n) → ((OpShelfSigTerm n) → A))) 
  | Sh vars (v x1) := (nth vars x1)  
  | Sh vars (linvOL x1 x2) := ((linv Sh) (evalOpB Sh vars x1) (evalOpB Sh vars x2))  
  | Sh vars (rinvOL x1 x2) := ((rinv Sh) (evalOpB Sh vars x1) (evalOpB Sh vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((ShelfSig A) → ((vector A n) → ((OpShelfSigTerm2 n A) → A))) 
  | Sh vars (v2 x1) := (nth vars x1)  
  | Sh vars (sing2 x1) := x1  
  | Sh vars (linvOL2 x1 x2) := ((linv Sh) (evalOp Sh vars x1) (evalOp Sh vars x2))  
  | Sh vars (rinvOL2 x1 x2) := ((rinv Sh) (evalOp Sh vars x1) (evalOp Sh vars x2))  
  def inductionB   {P : (ShelfSigTerm → Type)}  : ((∀ (x1 x2 : ShelfSigTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : ShelfSigTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : ShelfSigTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClShelfSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClShelfSigTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClShelfSigTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClShelfSigTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpShelfSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpShelfSigTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpShelfSigTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpShelfSigTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpShelfSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpShelfSigTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpShelfSigTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpShelfSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (ShelfSigTerm → (Staged ShelfSigTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClShelfSigTerm A) → (Staged (ClShelfSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpShelfSigTerm n) → (Staged (OpShelfSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpShelfSigTerm2 n A) → (Staged (OpShelfSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end ShelfSig