import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section QuasiInverse   
  structure QuasiInverse  (A : Type) : Type := 
       (inv : (A → A))
       (op : (A → (A → A)))
       (quasiInverse_inv_op_e : (∀ {x : A} , (op (op x (inv x)) x) = x))
       (quasiRightInverse_inv_op_e : (∀ {x : A} , (op (op (inv x) x) (inv x)) = (inv x))) 
  
  open QuasiInverse
  structure Sig  (AS : Type) : Type := 
       (invS : (AS → AS))
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (invP : ((Prod A A) → (Prod A A)))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (quasiInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (opP xP (invP xP)) xP) = xP))
       (quasiRightInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (opP (invP xP) xP) (invP xP)) = (invP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Qu1 : (QuasiInverse A1)) (Qu2 : (QuasiInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Qu1) x1)) = ((inv Qu2) (hom x1))))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Qu1) x1 x2)) = ((op Qu2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Qu1 : (QuasiInverse A1)) (Qu2 : (QuasiInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Qu1) x1) ((inv Qu2) y1)))))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Qu1) x1 x2) ((op Qu2) y1 y2)))))) 
  
  inductive QuasiInverseTerm   : Type  
     | invL : (QuasiInverseTerm → QuasiInverseTerm) 
     | opL : (QuasiInverseTerm → (QuasiInverseTerm → QuasiInverseTerm))  
      open QuasiInverseTerm 
  
  inductive ClQuasiInverseTerm  (A : Type) : Type  
     | sing : (A → ClQuasiInverseTerm) 
     | invCl : (ClQuasiInverseTerm → ClQuasiInverseTerm) 
     | opCl : (ClQuasiInverseTerm → (ClQuasiInverseTerm → ClQuasiInverseTerm))  
      open ClQuasiInverseTerm 
  
  inductive OpQuasiInverseTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpQuasiInverseTerm) 
     | invOL : (OpQuasiInverseTerm → OpQuasiInverseTerm) 
     | opOL : (OpQuasiInverseTerm → (OpQuasiInverseTerm → OpQuasiInverseTerm))  
      open OpQuasiInverseTerm 
  
  inductive OpQuasiInverseTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpQuasiInverseTerm2) 
     | sing2 : (A → OpQuasiInverseTerm2) 
     | invOL2 : (OpQuasiInverseTerm2 → OpQuasiInverseTerm2) 
     | opOL2 : (OpQuasiInverseTerm2 → (OpQuasiInverseTerm2 → OpQuasiInverseTerm2))  
      open OpQuasiInverseTerm2 
  
  def simplifyCl   {A : Type}  : ((ClQuasiInverseTerm A) → (ClQuasiInverseTerm A)) 
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpQuasiInverseTerm n) → (OpQuasiInverseTerm n)) 
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpQuasiInverseTerm2 n A) → (OpQuasiInverseTerm2 n A)) 
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((QuasiInverse A) → (QuasiInverseTerm → A)) 
  | Qu (invL x1) := ((inv Qu) (evalB Qu x1))  
  | Qu (opL x1 x2) := ((op Qu) (evalB Qu x1) (evalB Qu x2))  
  def evalCl   {A : Type}  : ((QuasiInverse A) → ((ClQuasiInverseTerm A) → A)) 
  | Qu (sing x1) := x1  
  | Qu (invCl x1) := ((inv Qu) (evalCl Qu x1))  
  | Qu (opCl x1 x2) := ((op Qu) (evalCl Qu x1) (evalCl Qu x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((QuasiInverse A) → ((vector A n) → ((OpQuasiInverseTerm n) → A))) 
  | Qu vars (v x1) := (nth vars x1)  
  | Qu vars (invOL x1) := ((inv Qu) (evalOpB Qu vars x1))  
  | Qu vars (opOL x1 x2) := ((op Qu) (evalOpB Qu vars x1) (evalOpB Qu vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((QuasiInverse A) → ((vector A n) → ((OpQuasiInverseTerm2 n A) → A))) 
  | Qu vars (v2 x1) := (nth vars x1)  
  | Qu vars (sing2 x1) := x1  
  | Qu vars (invOL2 x1) := ((inv Qu) (evalOp Qu vars x1))  
  | Qu vars (opOL2 x1 x2) := ((op Qu) (evalOp Qu vars x1) (evalOp Qu vars x2))  
  def inductionB   {P : (QuasiInverseTerm → Type)}  : ((∀ (x1 : QuasiInverseTerm) , ((P x1) → (P (invL x1)))) → ((∀ (x1 x2 : QuasiInverseTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : QuasiInverseTerm) , (P x)))) 
  | pinvl popl (invL x1) := (pinvl _ (inductionB pinvl popl x1))  
  | pinvl popl (opL x1 x2) := (popl _ _ (inductionB pinvl popl x1) (inductionB pinvl popl x2))  
  def inductionCl   {A : Type} {P : ((ClQuasiInverseTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClQuasiInverseTerm A)) , ((P x1) → (P (invCl x1)))) → ((∀ (x1 x2 : (ClQuasiInverseTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClQuasiInverseTerm A)) , (P x))))) 
  | psing pinvcl popcl (sing x1) := (psing x1)  
  | psing pinvcl popcl (invCl x1) := (pinvcl _ (inductionCl psing pinvcl popcl x1))  
  | psing pinvcl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pinvcl popcl x1) (inductionCl psing pinvcl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpQuasiInverseTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpQuasiInverseTerm n)) , ((P x1) → (P (invOL x1)))) → ((∀ (x1 x2 : (OpQuasiInverseTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpQuasiInverseTerm n)) , (P x))))) 
  | pv pinvol popol (v x1) := (pv x1)  
  | pv pinvol popol (invOL x1) := (pinvol _ (inductionOpB pv pinvol popol x1))  
  | pv pinvol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pinvol popol x1) (inductionOpB pv pinvol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpQuasiInverseTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpQuasiInverseTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → ((∀ (x1 x2 : (OpQuasiInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpQuasiInverseTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pinvol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pinvol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pinvol2 popol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 pinvol2 popol2 x1))  
  | pv2 psing2 pinvol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pinvol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 popol2 x2))  
  def stageB  : (QuasiInverseTerm → (Staged QuasiInverseTerm))
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClQuasiInverseTerm A) → (Staged (ClQuasiInverseTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpQuasiInverseTerm n) → (Staged (OpQuasiInverseTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpQuasiInverseTerm2 n A) → (Staged (OpQuasiInverseTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (invT : ((Repr A) → (Repr A)))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end QuasiInverse