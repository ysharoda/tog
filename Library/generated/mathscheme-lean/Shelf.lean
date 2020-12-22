import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Shelf   
  structure Shelf  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z))))
       (rightDistributive : (∀ {x y z : A} , (rinv (rinv y z) x) = (rinv (rinv y x) (rinv z x)))) 
  
  open Shelf
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP))))
       (rightDistributiveP : (∀ {xP yP zP : (Prod A A)} , (rinvP (rinvP yP zP) xP) = (rinvP (rinvP yP xP) (rinvP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Sh1 : (Shelf A1)) (Sh2 : (Shelf A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Sh1) x1 x2)) = ((linv Sh2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Sh1) x1 x2)) = ((rinv Sh2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Sh1 : (Shelf A1)) (Sh2 : (Shelf A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Sh1) x1 x2) ((linv Sh2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Sh1) x1 x2) ((rinv Sh2) y1 y2)))))) 
  
  inductive ShelfTerm   : Type  
     | linvL : (ShelfTerm → (ShelfTerm → ShelfTerm)) 
     | rinvL : (ShelfTerm → (ShelfTerm → ShelfTerm))  
      open ShelfTerm 
  
  inductive ClShelfTerm  (A : Type) : Type  
     | sing : (A → ClShelfTerm) 
     | linvCl : (ClShelfTerm → (ClShelfTerm → ClShelfTerm)) 
     | rinvCl : (ClShelfTerm → (ClShelfTerm → ClShelfTerm))  
      open ClShelfTerm 
  
  inductive OpShelfTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpShelfTerm) 
     | linvOL : (OpShelfTerm → (OpShelfTerm → OpShelfTerm)) 
     | rinvOL : (OpShelfTerm → (OpShelfTerm → OpShelfTerm))  
      open OpShelfTerm 
  
  inductive OpShelfTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpShelfTerm2) 
     | sing2 : (A → OpShelfTerm2) 
     | linvOL2 : (OpShelfTerm2 → (OpShelfTerm2 → OpShelfTerm2)) 
     | rinvOL2 : (OpShelfTerm2 → (OpShelfTerm2 → OpShelfTerm2))  
      open OpShelfTerm2 
  
  def simplifyCl   (A : Type)  : ((ClShelfTerm A) → (ClShelfTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpShelfTerm n) → (OpShelfTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpShelfTerm2 n A) → (OpShelfTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Shelf A) → (ShelfTerm → A)) 
  | Sh (linvL x1 x2) := ((linv Sh) (evalB Sh x1) (evalB Sh x2))  
  | Sh (rinvL x1 x2) := ((rinv Sh) (evalB Sh x1) (evalB Sh x2))  
  def evalCl   {A : Type}  : ((Shelf A) → ((ClShelfTerm A) → A)) 
  | Sh (sing x1) := x1  
  | Sh (linvCl x1 x2) := ((linv Sh) (evalCl Sh x1) (evalCl Sh x2))  
  | Sh (rinvCl x1 x2) := ((rinv Sh) (evalCl Sh x1) (evalCl Sh x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Shelf A) → ((vector A n) → ((OpShelfTerm n) → A))) 
  | Sh vars (v x1) := (nth vars x1)  
  | Sh vars (linvOL x1 x2) := ((linv Sh) (evalOpB Sh vars x1) (evalOpB Sh vars x2))  
  | Sh vars (rinvOL x1 x2) := ((rinv Sh) (evalOpB Sh vars x1) (evalOpB Sh vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Shelf A) → ((vector A n) → ((OpShelfTerm2 n A) → A))) 
  | Sh vars (v2 x1) := (nth vars x1)  
  | Sh vars (sing2 x1) := x1  
  | Sh vars (linvOL2 x1 x2) := ((linv Sh) (evalOp Sh vars x1) (evalOp Sh vars x2))  
  | Sh vars (rinvOL2 x1 x2) := ((rinv Sh) (evalOp Sh vars x1) (evalOp Sh vars x2))  
  def inductionB   (P : (ShelfTerm → Type))  : ((∀ (x1 x2 : ShelfTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : ShelfTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : ShelfTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   (A : Type) (P : ((ClShelfTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClShelfTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClShelfTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClShelfTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpShelfTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpShelfTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpShelfTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpShelfTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpShelfTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpShelfTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpShelfTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpShelfTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (ShelfTerm → (Staged ShelfTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClShelfTerm A) → (Staged (ClShelfTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpShelfTerm n) → (Staged (OpShelfTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpShelfTerm2 n A) → (Staged (OpShelfTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Shelf