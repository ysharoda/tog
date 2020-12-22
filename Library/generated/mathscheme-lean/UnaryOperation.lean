import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section UnaryOperation   
  structure UnaryOperation  (A : Type) : Type := 
       (prim : (A → A)) 
  
  open UnaryOperation
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Un1 : (UnaryOperation A1)) (Un2 : (UnaryOperation A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Un1) x1)) = ((prim Un2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Un1 : (UnaryOperation A1)) (Un2 : (UnaryOperation A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Un1) x1) ((prim Un2) y1))))) 
  
  inductive UnaryOperationTerm   : Type  
     | primL : (UnaryOperationTerm → UnaryOperationTerm)  
      open UnaryOperationTerm 
  
  inductive ClUnaryOperationTerm  (A : Type) : Type  
     | sing : (A → ClUnaryOperationTerm) 
     | primCl : (ClUnaryOperationTerm → ClUnaryOperationTerm)  
      open ClUnaryOperationTerm 
  
  inductive OpUnaryOperationTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpUnaryOperationTerm) 
     | primOL : (OpUnaryOperationTerm → OpUnaryOperationTerm)  
      open OpUnaryOperationTerm 
  
  inductive OpUnaryOperationTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpUnaryOperationTerm2) 
     | sing2 : (A → OpUnaryOperationTerm2) 
     | primOL2 : (OpUnaryOperationTerm2 → OpUnaryOperationTerm2)  
      open OpUnaryOperationTerm2 
  
  def simplifyCl   (A : Type)  : ((ClUnaryOperationTerm A) → (ClUnaryOperationTerm A)) 
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpUnaryOperationTerm n) → (OpUnaryOperationTerm n)) 
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpUnaryOperationTerm2 n A) → (OpUnaryOperationTerm2 n A)) 
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((UnaryOperation A) → (UnaryOperationTerm → A)) 
  | Un (primL x1) := ((prim Un) (evalB Un x1))  
  def evalCl   {A : Type}  : ((UnaryOperation A) → ((ClUnaryOperationTerm A) → A)) 
  | Un (sing x1) := x1  
  | Un (primCl x1) := ((prim Un) (evalCl Un x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((UnaryOperation A) → ((vector A n) → ((OpUnaryOperationTerm n) → A))) 
  | Un vars (v x1) := (nth vars x1)  
  | Un vars (primOL x1) := ((prim Un) (evalOpB Un vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((UnaryOperation A) → ((vector A n) → ((OpUnaryOperationTerm2 n A) → A))) 
  | Un vars (v2 x1) := (nth vars x1)  
  | Un vars (sing2 x1) := x1  
  | Un vars (primOL2 x1) := ((prim Un) (evalOp Un vars x1))  
  def inductionB   (P : (UnaryOperationTerm → Type))  : ((∀ (x1 : UnaryOperationTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : UnaryOperationTerm) , (P x))) 
  | ppriml (primL x1) := (ppriml _ (inductionB ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClUnaryOperationTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClUnaryOperationTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClUnaryOperationTerm A)) , (P x)))) 
  | psing pprimcl (sing x1) := (psing x1)  
  | psing pprimcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpUnaryOperationTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpUnaryOperationTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpUnaryOperationTerm n)) , (P x)))) 
  | pv pprimol (v x1) := (pv x1)  
  | pv pprimol (primOL x1) := (pprimol _ (inductionOpB pv pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpUnaryOperationTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpUnaryOperationTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpUnaryOperationTerm2 n A)) , (P x))))) 
  | pv2 psing2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 x1))  
  def stageB  : (UnaryOperationTerm → (Staged UnaryOperationTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClUnaryOperationTerm A) → (Staged (ClUnaryOperationTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpUnaryOperationTerm n) → (Staged (OpUnaryOperationTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpUnaryOperationTerm2 n A) → (Staged (OpUnaryOperationTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A))) 
  
end UnaryOperation