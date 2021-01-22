import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section UnaryDistributes   
  structure UnaryDistributes  (A : Type) : Type := 
       (prim : (A → A))
       (op : (A → (A → A)))
       (distribute_prim_op : (∀ {x y : A} , (prim (op x y)) = (op (prim x) (prim y)))) 
  
  open UnaryDistributes
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (distribute_prim_opP : (∀ {xP yP : (Prod A A)} , (primP (opP xP yP)) = (opP (primP xP) (primP yP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Un1 : (UnaryDistributes A1)) (Un2 : (UnaryDistributes A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Un1) x1)) = ((prim Un2) (hom x1))))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Un1) x1 x2)) = ((op Un2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Un1 : (UnaryDistributes A1)) (Un2 : (UnaryDistributes A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Un1) x1) ((prim Un2) y1)))))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Un1) x1 x2) ((op Un2) y1 y2)))))) 
  
  inductive UnaryDistributesTerm   : Type  
     | primL : (UnaryDistributesTerm → UnaryDistributesTerm) 
     | opL : (UnaryDistributesTerm → (UnaryDistributesTerm → UnaryDistributesTerm))  
      open UnaryDistributesTerm 
  
  inductive ClUnaryDistributesTerm  (A : Type) : Type  
     | sing : (A → ClUnaryDistributesTerm) 
     | primCl : (ClUnaryDistributesTerm → ClUnaryDistributesTerm) 
     | opCl : (ClUnaryDistributesTerm → (ClUnaryDistributesTerm → ClUnaryDistributesTerm))  
      open ClUnaryDistributesTerm 
  
  inductive OpUnaryDistributesTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpUnaryDistributesTerm) 
     | primOL : (OpUnaryDistributesTerm → OpUnaryDistributesTerm) 
     | opOL : (OpUnaryDistributesTerm → (OpUnaryDistributesTerm → OpUnaryDistributesTerm))  
      open OpUnaryDistributesTerm 
  
  inductive OpUnaryDistributesTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpUnaryDistributesTerm2) 
     | sing2 : (A → OpUnaryDistributesTerm2) 
     | primOL2 : (OpUnaryDistributesTerm2 → OpUnaryDistributesTerm2) 
     | opOL2 : (OpUnaryDistributesTerm2 → (OpUnaryDistributesTerm2 → OpUnaryDistributesTerm2))  
      open OpUnaryDistributesTerm2 
  
  def simplifyCl   {A : Type}  : ((ClUnaryDistributesTerm A) → (ClUnaryDistributesTerm A)) 
  | (opCl (primCl x) (primCl y)) := (primCl (opCl x y))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpUnaryDistributesTerm n) → (OpUnaryDistributesTerm n)) 
  | (opOL (primOL x) (primOL y)) := (primOL (opOL x y))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpUnaryDistributesTerm2 n A) → (OpUnaryDistributesTerm2 n A)) 
  | (opOL2 (primOL2 x) (primOL2 y)) := (primOL2 (opOL2 x y))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((UnaryDistributes A) → (UnaryDistributesTerm → A)) 
  | Un (primL x1) := ((prim Un) (evalB Un x1))  
  | Un (opL x1 x2) := ((op Un) (evalB Un x1) (evalB Un x2))  
  def evalCl   {A : Type}  : ((UnaryDistributes A) → ((ClUnaryDistributesTerm A) → A)) 
  | Un (sing x1) := x1  
  | Un (primCl x1) := ((prim Un) (evalCl Un x1))  
  | Un (opCl x1 x2) := ((op Un) (evalCl Un x1) (evalCl Un x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((UnaryDistributes A) → ((vector A n) → ((OpUnaryDistributesTerm n) → A))) 
  | Un vars (v x1) := (nth vars x1)  
  | Un vars (primOL x1) := ((prim Un) (evalOpB Un vars x1))  
  | Un vars (opOL x1 x2) := ((op Un) (evalOpB Un vars x1) (evalOpB Un vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((UnaryDistributes A) → ((vector A n) → ((OpUnaryDistributesTerm2 n A) → A))) 
  | Un vars (v2 x1) := (nth vars x1)  
  | Un vars (sing2 x1) := x1  
  | Un vars (primOL2 x1) := ((prim Un) (evalOp Un vars x1))  
  | Un vars (opOL2 x1 x2) := ((op Un) (evalOp Un vars x1) (evalOp Un vars x2))  
  def inductionB   {P : (UnaryDistributesTerm → Type)}  : ((∀ (x1 : UnaryDistributesTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : UnaryDistributesTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : UnaryDistributesTerm) , (P x)))) 
  | ppriml popl (primL x1) := (ppriml _ (inductionB ppriml popl x1))  
  | ppriml popl (opL x1 x2) := (popl _ _ (inductionB ppriml popl x1) (inductionB ppriml popl x2))  
  def inductionCl   {A : Type} {P : ((ClUnaryDistributesTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClUnaryDistributesTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClUnaryDistributesTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClUnaryDistributesTerm A)) , (P x))))) 
  | psing pprimcl popcl (sing x1) := (psing x1)  
  | psing pprimcl popcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl popcl x1))  
  | psing pprimcl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pprimcl popcl x1) (inductionCl psing pprimcl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpUnaryDistributesTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpUnaryDistributesTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpUnaryDistributesTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpUnaryDistributesTerm n)) , (P x))))) 
  | pv pprimol popol (v x1) := (pv x1)  
  | pv pprimol popol (primOL x1) := (pprimol _ (inductionOpB pv pprimol popol x1))  
  | pv pprimol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pprimol popol x1) (inductionOpB pv pprimol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpUnaryDistributesTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpUnaryDistributesTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpUnaryDistributesTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpUnaryDistributesTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 popol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 popol2 x1))  
  | pv2 psing2 pprimol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pprimol2 popol2 x1) (inductionOp pv2 psing2 pprimol2 popol2 x2))  
  def stageB  : (UnaryDistributesTerm → (Staged UnaryDistributesTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClUnaryDistributesTerm A) → (Staged (ClUnaryDistributesTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpUnaryDistributesTerm n) → (Staged (OpUnaryDistributesTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpUnaryDistributesTerm2 n A) → (Staged (OpUnaryDistributesTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end UnaryDistributes