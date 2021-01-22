import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Rack   
  structure Rack  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z))))
       (rightDistributive : (∀ {x y z : A} , (rinv (rinv y z) x) = (rinv (rinv y x) (rinv z x))))
       (leftInverse : (∀ {x y : A} , (rinv (linv x y) x) = y))
       (rightInverse : (∀ {x y : A} , (linv x (rinv y x)) = y)) 
  
  open Rack
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP))))
       (rightDistributiveP : (∀ {xP yP zP : (Prod A A)} , (rinvP (rinvP yP zP) xP) = (rinvP (rinvP yP xP) (rinvP zP xP))))
       (leftInverseP : (∀ {xP yP : (Prod A A)} , (rinvP (linvP xP yP) xP) = yP))
       (rightInverseP : (∀ {xP yP : (Prod A A)} , (linvP xP (rinvP yP xP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ra1 : (Rack A1)) (Ra2 : (Rack A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Ra1) x1 x2)) = ((linv Ra2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Ra1) x1 x2)) = ((rinv Ra2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ra1 : (Rack A1)) (Ra2 : (Rack A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Ra1) x1 x2) ((linv Ra2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ra1) x1 x2) ((rinv Ra2) y1 y2)))))) 
  
  inductive RackTerm   : Type  
     | linvL : (RackTerm → (RackTerm → RackTerm)) 
     | rinvL : (RackTerm → (RackTerm → RackTerm))  
      open RackTerm 
  
  inductive ClRackTerm  (A : Type) : Type  
     | sing : (A → ClRackTerm) 
     | linvCl : (ClRackTerm → (ClRackTerm → ClRackTerm)) 
     | rinvCl : (ClRackTerm → (ClRackTerm → ClRackTerm))  
      open ClRackTerm 
  
  inductive OpRackTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRackTerm) 
     | linvOL : (OpRackTerm → (OpRackTerm → OpRackTerm)) 
     | rinvOL : (OpRackTerm → (OpRackTerm → OpRackTerm))  
      open OpRackTerm 
  
  inductive OpRackTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRackTerm2) 
     | sing2 : (A → OpRackTerm2) 
     | linvOL2 : (OpRackTerm2 → (OpRackTerm2 → OpRackTerm2)) 
     | rinvOL2 : (OpRackTerm2 → (OpRackTerm2 → OpRackTerm2))  
      open OpRackTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRackTerm A) → (ClRackTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRackTerm n) → (OpRackTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRackTerm2 n A) → (OpRackTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Rack A) → (RackTerm → A)) 
  | Ra (linvL x1 x2) := ((linv Ra) (evalB Ra x1) (evalB Ra x2))  
  | Ra (rinvL x1 x2) := ((rinv Ra) (evalB Ra x1) (evalB Ra x2))  
  def evalCl   {A : Type}  : ((Rack A) → ((ClRackTerm A) → A)) 
  | Ra (sing x1) := x1  
  | Ra (linvCl x1 x2) := ((linv Ra) (evalCl Ra x1) (evalCl Ra x2))  
  | Ra (rinvCl x1 x2) := ((rinv Ra) (evalCl Ra x1) (evalCl Ra x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Rack A) → ((vector A n) → ((OpRackTerm n) → A))) 
  | Ra vars (v x1) := (nth vars x1)  
  | Ra vars (linvOL x1 x2) := ((linv Ra) (evalOpB Ra vars x1) (evalOpB Ra vars x2))  
  | Ra vars (rinvOL x1 x2) := ((rinv Ra) (evalOpB Ra vars x1) (evalOpB Ra vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Rack A) → ((vector A n) → ((OpRackTerm2 n A) → A))) 
  | Ra vars (v2 x1) := (nth vars x1)  
  | Ra vars (sing2 x1) := x1  
  | Ra vars (linvOL2 x1 x2) := ((linv Ra) (evalOp Ra vars x1) (evalOp Ra vars x2))  
  | Ra vars (rinvOL2 x1 x2) := ((rinv Ra) (evalOp Ra vars x1) (evalOp Ra vars x2))  
  def inductionB   {P : (RackTerm → Type)}  : ((∀ (x1 x2 : RackTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : RackTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : RackTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRackTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRackTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClRackTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClRackTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRackTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRackTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpRackTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpRackTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRackTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRackTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRackTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpRackTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (RackTerm → (Staged RackTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRackTerm A) → (Staged (ClRackTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRackTerm n) → (Staged (OpRackTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRackTerm2 n A) → (Staged (OpRackTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Rack