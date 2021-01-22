import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PseudoInvolution   
  structure PseudoInvolution  (A : Type) : Type := 
       (inv : (A → A))
       (op : (A → (A → A)))
       (quasiRightInverse_inv_op_e : (∀ {x : A} , (op (op (inv x) x) (inv x)) = (inv x))) 
  
  open PseudoInvolution
  structure Sig  (AS : Type) : Type := 
       (invS : (AS → AS))
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (invP : ((Prod A A) → (Prod A A)))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (quasiRightInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (opP (invP xP) xP) (invP xP)) = (invP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ps1 : (PseudoInvolution A1)) (Ps2 : (PseudoInvolution A2)) : Type := 
       (hom : (A1 → A2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Ps1) x1)) = ((inv Ps2) (hom x1))))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ps1) x1 x2)) = ((op Ps2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ps1 : (PseudoInvolution A1)) (Ps2 : (PseudoInvolution A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Ps1) x1) ((inv Ps2) y1)))))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ps1) x1 x2) ((op Ps2) y1 y2)))))) 
  
  inductive PseudoInvolutionTerm   : Type  
     | invL : (PseudoInvolutionTerm → PseudoInvolutionTerm) 
     | opL : (PseudoInvolutionTerm → (PseudoInvolutionTerm → PseudoInvolutionTerm))  
      open PseudoInvolutionTerm 
  
  inductive ClPseudoInvolutionTerm  (A : Type) : Type  
     | sing : (A → ClPseudoInvolutionTerm) 
     | invCl : (ClPseudoInvolutionTerm → ClPseudoInvolutionTerm) 
     | opCl : (ClPseudoInvolutionTerm → (ClPseudoInvolutionTerm → ClPseudoInvolutionTerm))  
      open ClPseudoInvolutionTerm 
  
  inductive OpPseudoInvolutionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPseudoInvolutionTerm) 
     | invOL : (OpPseudoInvolutionTerm → OpPseudoInvolutionTerm) 
     | opOL : (OpPseudoInvolutionTerm → (OpPseudoInvolutionTerm → OpPseudoInvolutionTerm))  
      open OpPseudoInvolutionTerm 
  
  inductive OpPseudoInvolutionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPseudoInvolutionTerm2) 
     | sing2 : (A → OpPseudoInvolutionTerm2) 
     | invOL2 : (OpPseudoInvolutionTerm2 → OpPseudoInvolutionTerm2) 
     | opOL2 : (OpPseudoInvolutionTerm2 → (OpPseudoInvolutionTerm2 → OpPseudoInvolutionTerm2))  
      open OpPseudoInvolutionTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPseudoInvolutionTerm A) → (ClPseudoInvolutionTerm A)) 
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPseudoInvolutionTerm n) → (OpPseudoInvolutionTerm n)) 
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPseudoInvolutionTerm2 n A) → (OpPseudoInvolutionTerm2 n A)) 
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PseudoInvolution A) → (PseudoInvolutionTerm → A)) 
  | Ps (invL x1) := ((inv Ps) (evalB Ps x1))  
  | Ps (opL x1 x2) := ((op Ps) (evalB Ps x1) (evalB Ps x2))  
  def evalCl   {A : Type}  : ((PseudoInvolution A) → ((ClPseudoInvolutionTerm A) → A)) 
  | Ps (sing x1) := x1  
  | Ps (invCl x1) := ((inv Ps) (evalCl Ps x1))  
  | Ps (opCl x1 x2) := ((op Ps) (evalCl Ps x1) (evalCl Ps x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((PseudoInvolution A) → ((vector A n) → ((OpPseudoInvolutionTerm n) → A))) 
  | Ps vars (v x1) := (nth vars x1)  
  | Ps vars (invOL x1) := ((inv Ps) (evalOpB Ps vars x1))  
  | Ps vars (opOL x1 x2) := ((op Ps) (evalOpB Ps vars x1) (evalOpB Ps vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((PseudoInvolution A) → ((vector A n) → ((OpPseudoInvolutionTerm2 n A) → A))) 
  | Ps vars (v2 x1) := (nth vars x1)  
  | Ps vars (sing2 x1) := x1  
  | Ps vars (invOL2 x1) := ((inv Ps) (evalOp Ps vars x1))  
  | Ps vars (opOL2 x1 x2) := ((op Ps) (evalOp Ps vars x1) (evalOp Ps vars x2))  
  def inductionB   {P : (PseudoInvolutionTerm → Type)}  : ((∀ (x1 : PseudoInvolutionTerm) , ((P x1) → (P (invL x1)))) → ((∀ (x1 x2 : PseudoInvolutionTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : PseudoInvolutionTerm) , (P x)))) 
  | pinvl popl (invL x1) := (pinvl _ (inductionB pinvl popl x1))  
  | pinvl popl (opL x1 x2) := (popl _ _ (inductionB pinvl popl x1) (inductionB pinvl popl x2))  
  def inductionCl   {A : Type} {P : ((ClPseudoInvolutionTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClPseudoInvolutionTerm A)) , ((P x1) → (P (invCl x1)))) → ((∀ (x1 x2 : (ClPseudoInvolutionTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClPseudoInvolutionTerm A)) , (P x))))) 
  | psing pinvcl popcl (sing x1) := (psing x1)  
  | psing pinvcl popcl (invCl x1) := (pinvcl _ (inductionCl psing pinvcl popcl x1))  
  | psing pinvcl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pinvcl popcl x1) (inductionCl psing pinvcl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpPseudoInvolutionTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpPseudoInvolutionTerm n)) , ((P x1) → (P (invOL x1)))) → ((∀ (x1 x2 : (OpPseudoInvolutionTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpPseudoInvolutionTerm n)) , (P x))))) 
  | pv pinvol popol (v x1) := (pv x1)  
  | pv pinvol popol (invOL x1) := (pinvol _ (inductionOpB pv pinvol popol x1))  
  | pv pinvol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pinvol popol x1) (inductionOpB pv pinvol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPseudoInvolutionTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpPseudoInvolutionTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → ((∀ (x1 x2 : (OpPseudoInvolutionTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpPseudoInvolutionTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pinvol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pinvol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pinvol2 popol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 pinvol2 popol2 x1))  
  | pv2 psing2 pinvol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pinvol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 popol2 x2))  
  def stageB  : (PseudoInvolutionTerm → (Staged PseudoInvolutionTerm))
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClPseudoInvolutionTerm A) → (Staged (ClPseudoInvolutionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpPseudoInvolutionTerm n) → (Staged (OpPseudoInvolutionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPseudoInvolutionTerm2 n A) → (Staged (OpPseudoInvolutionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (invT : ((Repr A) → (Repr A)))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end PseudoInvolution