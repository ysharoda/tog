import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MoufangQuasiGroup   
  structure MoufangQuasiGroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (linv : (A → (A → A)))
       (leftCancel : (∀ {x y : A} , (op x (linv x y)) = y))
       (lefCancelOp : (∀ {x y : A} , (linv x (op x y)) = y))
       (rinv : (A → (A → A)))
       (rightCancel : (∀ {x y : A} , (op (rinv y x) x) = y))
       (rightCancelOp : (∀ {x y : A} , (rinv (op y x) x) = y))
       (moufangLaw : (∀ {e x y z : A} , ((op y e) = y → (op (op (op x y) z) x) = (op x (op y (op (op e z) x)))))) 
  
  open MoufangQuasiGroup
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
       (moufangLawP : (∀ {eP xP yP zP : (Prod A A)} , ((opP yP eP) = yP → (opP (opP (opP xP yP) zP) xP) = (opP xP (opP yP (opP (opP eP zP) xP)))))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mo1 : (MoufangQuasiGroup A1)) (Mo2 : (MoufangQuasiGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Mo1) x1 x2)) = ((op Mo2) (hom x1) (hom x2))))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Mo1) x1 x2)) = ((linv Mo2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Mo1) x1 x2)) = ((rinv Mo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mo1 : (MoufangQuasiGroup A1)) (Mo2 : (MoufangQuasiGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2))))))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Mo1) x1 x2) ((linv Mo2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Mo1) x1 x2) ((rinv Mo2) y1 y2)))))) 
  
  inductive MoufangQuasiGroupTerm   : Type  
     | opL : (MoufangQuasiGroupTerm → (MoufangQuasiGroupTerm → MoufangQuasiGroupTerm)) 
     | linvL : (MoufangQuasiGroupTerm → (MoufangQuasiGroupTerm → MoufangQuasiGroupTerm)) 
     | rinvL : (MoufangQuasiGroupTerm → (MoufangQuasiGroupTerm → MoufangQuasiGroupTerm))  
      open MoufangQuasiGroupTerm 
  
  inductive ClMoufangQuasiGroupTerm  (A : Type) : Type  
     | sing : (A → ClMoufangQuasiGroupTerm) 
     | opCl : (ClMoufangQuasiGroupTerm → (ClMoufangQuasiGroupTerm → ClMoufangQuasiGroupTerm)) 
     | linvCl : (ClMoufangQuasiGroupTerm → (ClMoufangQuasiGroupTerm → ClMoufangQuasiGroupTerm)) 
     | rinvCl : (ClMoufangQuasiGroupTerm → (ClMoufangQuasiGroupTerm → ClMoufangQuasiGroupTerm))  
      open ClMoufangQuasiGroupTerm 
  
  inductive OpMoufangQuasiGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMoufangQuasiGroupTerm) 
     | opOL : (OpMoufangQuasiGroupTerm → (OpMoufangQuasiGroupTerm → OpMoufangQuasiGroupTerm)) 
     | linvOL : (OpMoufangQuasiGroupTerm → (OpMoufangQuasiGroupTerm → OpMoufangQuasiGroupTerm)) 
     | rinvOL : (OpMoufangQuasiGroupTerm → (OpMoufangQuasiGroupTerm → OpMoufangQuasiGroupTerm))  
      open OpMoufangQuasiGroupTerm 
  
  inductive OpMoufangQuasiGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMoufangQuasiGroupTerm2) 
     | sing2 : (A → OpMoufangQuasiGroupTerm2) 
     | opOL2 : (OpMoufangQuasiGroupTerm2 → (OpMoufangQuasiGroupTerm2 → OpMoufangQuasiGroupTerm2)) 
     | linvOL2 : (OpMoufangQuasiGroupTerm2 → (OpMoufangQuasiGroupTerm2 → OpMoufangQuasiGroupTerm2)) 
     | rinvOL2 : (OpMoufangQuasiGroupTerm2 → (OpMoufangQuasiGroupTerm2 → OpMoufangQuasiGroupTerm2))  
      open OpMoufangQuasiGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMoufangQuasiGroupTerm A) → (ClMoufangQuasiGroupTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMoufangQuasiGroupTerm n) → (OpMoufangQuasiGroupTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMoufangQuasiGroupTerm2 n A) → (OpMoufangQuasiGroupTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MoufangQuasiGroup A) → (MoufangQuasiGroupTerm → A)) 
  | Mo (opL x1 x2) := ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  | Mo (linvL x1 x2) := ((linv Mo) (evalB Mo x1) (evalB Mo x2))  
  | Mo (rinvL x1 x2) := ((rinv Mo) (evalB Mo x1) (evalB Mo x2))  
  def evalCl   {A : Type}  : ((MoufangQuasiGroup A) → ((ClMoufangQuasiGroupTerm A) → A)) 
  | Mo (sing x1) := x1  
  | Mo (opCl x1 x2) := ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  | Mo (linvCl x1 x2) := ((linv Mo) (evalCl Mo x1) (evalCl Mo x2))  
  | Mo (rinvCl x1 x2) := ((rinv Mo) (evalCl Mo x1) (evalCl Mo x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MoufangQuasiGroup A) → ((vector A n) → ((OpMoufangQuasiGroupTerm n) → A))) 
  | Mo vars (v x1) := (nth vars x1)  
  | Mo vars (opOL x1 x2) := ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  | Mo vars (linvOL x1 x2) := ((linv Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  | Mo vars (rinvOL x1 x2) := ((rinv Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((MoufangQuasiGroup A) → ((vector A n) → ((OpMoufangQuasiGroupTerm2 n A) → A))) 
  | Mo vars (v2 x1) := (nth vars x1)  
  | Mo vars (sing2 x1) := x1  
  | Mo vars (opOL2 x1 x2) := ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  | Mo vars (linvOL2 x1 x2) := ((linv Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  | Mo vars (rinvOL2 x1 x2) := ((rinv Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  def inductionB   (P : (MoufangQuasiGroupTerm → Type))  : ((∀ (x1 x2 : MoufangQuasiGroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((∀ (x1 x2 : MoufangQuasiGroupTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : MoufangQuasiGroupTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : MoufangQuasiGroupTerm) , (P x))))) 
  | popl plinvl prinvl (opL x1 x2) := (popl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  | popl plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  | popl plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB popl plinvl prinvl x1) (inductionB popl plinvl prinvl x2))  
  def inductionCl   (A : Type) (P : ((ClMoufangQuasiGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMoufangQuasiGroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((∀ (x1 x2 : (ClMoufangQuasiGroupTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClMoufangQuasiGroupTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClMoufangQuasiGroupTerm A)) , (P x)))))) 
  | psing popcl plinvcl prinvcl (sing x1) := (psing x1)  
  | psing popcl plinvcl prinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  | psing popcl plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  | psing popcl plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing popcl plinvcl prinvcl x1) (inductionCl psing popcl plinvcl prinvcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpMoufangQuasiGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMoufangQuasiGroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((∀ (x1 x2 : (OpMoufangQuasiGroupTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpMoufangQuasiGroupTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpMoufangQuasiGroupTerm n)) , (P x)))))) 
  | pv popol plinvol prinvol (v x1) := (pv x1)  
  | pv popol plinvol prinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  | pv popol plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  | pv popol plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv popol plinvol prinvol x1) (inductionOpB pv popol plinvol prinvol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMoufangQuasiGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMoufangQuasiGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((∀ (x1 x2 : (OpMoufangQuasiGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpMoufangQuasiGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpMoufangQuasiGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  | pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  | pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 popol2 plinvol2 prinvol2 x2))  
  def stageB  : (MoufangQuasiGroupTerm → (Staged MoufangQuasiGroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClMoufangQuasiGroupTerm A) → (Staged (ClMoufangQuasiGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpMoufangQuasiGroupTerm n) → (Staged (OpMoufangQuasiGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMoufangQuasiGroupTerm2 n A) → (Staged (OpMoufangQuasiGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MoufangQuasiGroup