import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PseudoInverse   
  structure PseudoInverse  (A : Type) : Type := 
       (inv : (A → A))
       (op : (A → (A → A)))
       (quasiInverse_inv_op_e : (∀ {x : A} , (op (op x (inv x)) x) = x)) 
  
  open PseudoInverse
  structure Sig  (AS : Type) : Type := 
       (invS : (AS → AS))
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (invP : ((Prod A A) → (Prod A A)))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (quasiInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (opP xP (invP xP)) xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ps1 : (PseudoInverse A1)) (Ps2 : (PseudoInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Ps1) x1)) = ((inv Ps2) (hom x1))))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ps1) x1 x2)) = ((op Ps2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ps1 : (PseudoInverse A1)) (Ps2 : (PseudoInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Ps1) x1) ((inv Ps2) y1)))))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ps1) x1 x2) ((op Ps2) y1 y2)))))) 
  
  inductive PseudoInverseTerm   : Type  
     | invL : (PseudoInverseTerm → PseudoInverseTerm) 
     | opL : (PseudoInverseTerm → (PseudoInverseTerm → PseudoInverseTerm))  
      open PseudoInverseTerm 
  
  inductive ClPseudoInverseTerm  (A : Type) : Type  
     | sing : (A → ClPseudoInverseTerm) 
     | invCl : (ClPseudoInverseTerm → ClPseudoInverseTerm) 
     | opCl : (ClPseudoInverseTerm → (ClPseudoInverseTerm → ClPseudoInverseTerm))  
      open ClPseudoInverseTerm 
  
  inductive OpPseudoInverseTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPseudoInverseTerm) 
     | invOL : (OpPseudoInverseTerm → OpPseudoInverseTerm) 
     | opOL : (OpPseudoInverseTerm → (OpPseudoInverseTerm → OpPseudoInverseTerm))  
      open OpPseudoInverseTerm 
  
  inductive OpPseudoInverseTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPseudoInverseTerm2) 
     | sing2 : (A → OpPseudoInverseTerm2) 
     | invOL2 : (OpPseudoInverseTerm2 → OpPseudoInverseTerm2) 
     | opOL2 : (OpPseudoInverseTerm2 → (OpPseudoInverseTerm2 → OpPseudoInverseTerm2))  
      open OpPseudoInverseTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPseudoInverseTerm A) → (ClPseudoInverseTerm A)) 
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPseudoInverseTerm n) → (OpPseudoInverseTerm n)) 
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPseudoInverseTerm2 n A) → (OpPseudoInverseTerm2 n A)) 
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PseudoInverse A) → (PseudoInverseTerm → A)) 
  | Ps (invL x1) := ((inv Ps) (evalB Ps x1))  
  | Ps (opL x1 x2) := ((op Ps) (evalB Ps x1) (evalB Ps x2))  
  def evalCl   {A : Type}  : ((PseudoInverse A) → ((ClPseudoInverseTerm A) → A)) 
  | Ps (sing x1) := x1  
  | Ps (invCl x1) := ((inv Ps) (evalCl Ps x1))  
  | Ps (opCl x1 x2) := ((op Ps) (evalCl Ps x1) (evalCl Ps x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((PseudoInverse A) → ((vector A n) → ((OpPseudoInverseTerm n) → A))) 
  | Ps vars (v x1) := (nth vars x1)  
  | Ps vars (invOL x1) := ((inv Ps) (evalOpB Ps vars x1))  
  | Ps vars (opOL x1 x2) := ((op Ps) (evalOpB Ps vars x1) (evalOpB Ps vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((PseudoInverse A) → ((vector A n) → ((OpPseudoInverseTerm2 n A) → A))) 
  | Ps vars (v2 x1) := (nth vars x1)  
  | Ps vars (sing2 x1) := x1  
  | Ps vars (invOL2 x1) := ((inv Ps) (evalOp Ps vars x1))  
  | Ps vars (opOL2 x1 x2) := ((op Ps) (evalOp Ps vars x1) (evalOp Ps vars x2))  
  def inductionB   (P : (PseudoInverseTerm → Type))  : ((∀ (x1 : PseudoInverseTerm) , ((P x1) → (P (invL x1)))) → ((∀ (x1 x2 : PseudoInverseTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : PseudoInverseTerm) , (P x)))) 
  | pinvl popl (invL x1) := (pinvl _ (inductionB pinvl popl x1))  
  | pinvl popl (opL x1 x2) := (popl _ _ (inductionB pinvl popl x1) (inductionB pinvl popl x2))  
  def inductionCl   (A : Type) (P : ((ClPseudoInverseTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClPseudoInverseTerm A)) , ((P x1) → (P (invCl x1)))) → ((∀ (x1 x2 : (ClPseudoInverseTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClPseudoInverseTerm A)) , (P x))))) 
  | psing pinvcl popcl (sing x1) := (psing x1)  
  | psing pinvcl popcl (invCl x1) := (pinvcl _ (inductionCl psing pinvcl popcl x1))  
  | psing pinvcl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pinvcl popcl x1) (inductionCl psing pinvcl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpPseudoInverseTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpPseudoInverseTerm n)) , ((P x1) → (P (invOL x1)))) → ((∀ (x1 x2 : (OpPseudoInverseTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpPseudoInverseTerm n)) , (P x))))) 
  | pv pinvol popol (v x1) := (pv x1)  
  | pv pinvol popol (invOL x1) := (pinvol _ (inductionOpB pv pinvol popol x1))  
  | pv pinvol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pinvol popol x1) (inductionOpB pv pinvol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPseudoInverseTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpPseudoInverseTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → ((∀ (x1 x2 : (OpPseudoInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpPseudoInverseTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pinvol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pinvol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pinvol2 popol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 pinvol2 popol2 x1))  
  | pv2 psing2 pinvol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pinvol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 popol2 x2))  
  def stageB  : (PseudoInverseTerm → (Staged PseudoInverseTerm))
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClPseudoInverseTerm A) → (Staged (ClPseudoInverseTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpPseudoInverseTerm n) → (Staged (OpPseudoInverseTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPseudoInverseTerm2 n A) → (Staged (OpPseudoInverseTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (invT : ((Repr A) → (Repr A)))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end PseudoInverse