import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RegularSemigroup   
  structure RegularSemigroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (inv : (A → A))
       (quasiInverse_inv_op_e : (∀ {x : A} , (op (op x (inv x)) x) = x)) 
  
  open RegularSemigroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (invP : ((Prod A A) → (Prod A A)))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (quasiInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (opP xP (invP xP)) xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Re1 : (RegularSemigroup A1)) (Re2 : (RegularSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Re1) x1 x2)) = ((op Re2) (hom x1) (hom x2))))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Re1) x1)) = ((inv Re2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Re1 : (RegularSemigroup A1)) (Re2 : (RegularSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Re1) x1 x2) ((op Re2) y1 y2))))))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Re1) x1) ((inv Re2) y1))))) 
  
  inductive RegularSemigroupTerm   : Type  
     | opL : (RegularSemigroupTerm → (RegularSemigroupTerm → RegularSemigroupTerm)) 
     | invL : (RegularSemigroupTerm → RegularSemigroupTerm)  
      open RegularSemigroupTerm 
  
  inductive ClRegularSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClRegularSemigroupTerm) 
     | opCl : (ClRegularSemigroupTerm → (ClRegularSemigroupTerm → ClRegularSemigroupTerm)) 
     | invCl : (ClRegularSemigroupTerm → ClRegularSemigroupTerm)  
      open ClRegularSemigroupTerm 
  
  inductive OpRegularSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRegularSemigroupTerm) 
     | opOL : (OpRegularSemigroupTerm → (OpRegularSemigroupTerm → OpRegularSemigroupTerm)) 
     | invOL : (OpRegularSemigroupTerm → OpRegularSemigroupTerm)  
      open OpRegularSemigroupTerm 
  
  inductive OpRegularSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRegularSemigroupTerm2) 
     | sing2 : (A → OpRegularSemigroupTerm2) 
     | opOL2 : (OpRegularSemigroupTerm2 → (OpRegularSemigroupTerm2 → OpRegularSemigroupTerm2)) 
     | invOL2 : (OpRegularSemigroupTerm2 → OpRegularSemigroupTerm2)  
      open OpRegularSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRegularSemigroupTerm A) → (ClRegularSemigroupTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRegularSemigroupTerm n) → (OpRegularSemigroupTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRegularSemigroupTerm2 n A) → (OpRegularSemigroupTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RegularSemigroup A) → (RegularSemigroupTerm → A)) 
  | Re (opL x1 x2) := ((op Re) (evalB Re x1) (evalB Re x2))  
  | Re (invL x1) := ((inv Re) (evalB Re x1))  
  def evalCl   {A : Type}  : ((RegularSemigroup A) → ((ClRegularSemigroupTerm A) → A)) 
  | Re (sing x1) := x1  
  | Re (opCl x1 x2) := ((op Re) (evalCl Re x1) (evalCl Re x2))  
  | Re (invCl x1) := ((inv Re) (evalCl Re x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((RegularSemigroup A) → ((vector A n) → ((OpRegularSemigroupTerm n) → A))) 
  | Re vars (v x1) := (nth vars x1)  
  | Re vars (opOL x1 x2) := ((op Re) (evalOpB Re vars x1) (evalOpB Re vars x2))  
  | Re vars (invOL x1) := ((inv Re) (evalOpB Re vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((RegularSemigroup A) → ((vector A n) → ((OpRegularSemigroupTerm2 n A) → A))) 
  | Re vars (v2 x1) := (nth vars x1)  
  | Re vars (sing2 x1) := x1  
  | Re vars (opOL2 x1 x2) := ((op Re) (evalOp Re vars x1) (evalOp Re vars x2))  
  | Re vars (invOL2 x1) := ((inv Re) (evalOp Re vars x1))  
  def inductionB   (P : (RegularSemigroupTerm → Type))  : ((∀ (x1 x2 : RegularSemigroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((∀ (x1 : RegularSemigroupTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : RegularSemigroupTerm) , (P x)))) 
  | popl pinvl (opL x1 x2) := (popl _ _ (inductionB popl pinvl x1) (inductionB popl pinvl x2))  
  | popl pinvl (invL x1) := (pinvl _ (inductionB popl pinvl x1))  
  def inductionCl   (A : Type) (P : ((ClRegularSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRegularSemigroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((∀ (x1 : (ClRegularSemigroupTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClRegularSemigroupTerm A)) , (P x))))) 
  | psing popcl pinvcl (sing x1) := (psing x1)  
  | psing popcl pinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pinvcl x1) (inductionCl psing popcl pinvcl x2))  
  | psing popcl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing popcl pinvcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpRegularSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRegularSemigroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((∀ (x1 : (OpRegularSemigroupTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpRegularSemigroupTerm n)) , (P x))))) 
  | pv popol pinvol (v x1) := (pv x1)  
  | pv popol pinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol pinvol x1) (inductionOpB pv popol pinvol x2))  
  | pv popol pinvol (invOL x1) := (pinvol _ (inductionOpB pv popol pinvol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRegularSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRegularSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((∀ (x1 : (OpRegularSemigroupTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpRegularSemigroupTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 pinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 pinvol2 x1) (inductionOp pv2 psing2 popol2 pinvol2 x2))  
  | pv2 psing2 popol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 popol2 pinvol2 x1))  
  def stageB  : (RegularSemigroupTerm → (Staged RegularSemigroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClRegularSemigroupTerm A) → (Staged (ClRegularSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpRegularSemigroupTerm n) → (Staged (OpRegularSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRegularSemigroupTerm2 n A) → (Staged (OpRegularSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (invT : ((Repr A) → (Repr A))) 
  
end RegularSemigroup