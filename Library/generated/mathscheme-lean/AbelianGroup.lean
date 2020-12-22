import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AbelianGroup   
  structure AbelianGroup  (A : Type) : Type := 
       (one : A)
       (times : (A → (A → A)))
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (inv : (A → A))
       (leftInverse_inv_op_one : (∀ {x : A} , (times x (inv x)) = one))
       (rightInverse_inv_op_one : (∀ {x : A} , (times (inv x) x) = one))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x))) 
  
  open AbelianGroup
  structure Sig  (AS : Type) : Type := 
       (oneS : AS)
       (timesS : (AS → (AS → AS)))
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (invP : ((Prod A A) → (Prod A A)))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP xP (invP xP)) = oneP))
       (rightInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP (invP xP) xP) = oneP))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ab1 : (AbelianGroup A1)) (Ab2 : (AbelianGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one Ab1)) = (one Ab2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ab1) x1 x2)) = ((times Ab2) (hom x1) (hom x2))))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Ab1) x1)) = ((inv Ab2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ab1 : (AbelianGroup A1)) (Ab2 : (AbelianGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one Ab1) (one Ab2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ab1) x1 x2) ((times Ab2) y1 y2))))))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Ab1) x1) ((inv Ab2) y1))))) 
  
  inductive AbelianGroupTerm   : Type  
     | oneL : AbelianGroupTerm 
     | timesL : (AbelianGroupTerm → (AbelianGroupTerm → AbelianGroupTerm)) 
     | invL : (AbelianGroupTerm → AbelianGroupTerm)  
      open AbelianGroupTerm 
  
  inductive ClAbelianGroupTerm  (A : Type) : Type  
     | sing : (A → ClAbelianGroupTerm) 
     | oneCl : ClAbelianGroupTerm 
     | timesCl : (ClAbelianGroupTerm → (ClAbelianGroupTerm → ClAbelianGroupTerm)) 
     | invCl : (ClAbelianGroupTerm → ClAbelianGroupTerm)  
      open ClAbelianGroupTerm 
  
  inductive OpAbelianGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAbelianGroupTerm) 
     | oneOL : OpAbelianGroupTerm 
     | timesOL : (OpAbelianGroupTerm → (OpAbelianGroupTerm → OpAbelianGroupTerm)) 
     | invOL : (OpAbelianGroupTerm → OpAbelianGroupTerm)  
      open OpAbelianGroupTerm 
  
  inductive OpAbelianGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAbelianGroupTerm2) 
     | sing2 : (A → OpAbelianGroupTerm2) 
     | oneOL2 : OpAbelianGroupTerm2 
     | timesOL2 : (OpAbelianGroupTerm2 → (OpAbelianGroupTerm2 → OpAbelianGroupTerm2)) 
     | invOL2 : (OpAbelianGroupTerm2 → OpAbelianGroupTerm2)  
      open OpAbelianGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAbelianGroupTerm A) → (ClAbelianGroupTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | oneCl := oneCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAbelianGroupTerm n) → (OpAbelianGroupTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | oneOL := oneOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAbelianGroupTerm2 n A) → (OpAbelianGroupTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | oneOL2 := oneOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AbelianGroup A) → (AbelianGroupTerm → A)) 
  | Ab oneL := (one Ab)  
  | Ab (timesL x1 x2) := ((times Ab) (evalB Ab x1) (evalB Ab x2))  
  | Ab (invL x1) := ((inv Ab) (evalB Ab x1))  
  def evalCl   {A : Type}  : ((AbelianGroup A) → ((ClAbelianGroupTerm A) → A)) 
  | Ab (sing x1) := x1  
  | Ab oneCl := (one Ab)  
  | Ab (timesCl x1 x2) := ((times Ab) (evalCl Ab x1) (evalCl Ab x2))  
  | Ab (invCl x1) := ((inv Ab) (evalCl Ab x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AbelianGroup A) → ((vector A n) → ((OpAbelianGroupTerm n) → A))) 
  | Ab vars (v x1) := (nth vars x1)  
  | Ab vars oneOL := (one Ab)  
  | Ab vars (timesOL x1 x2) := ((times Ab) (evalOpB Ab vars x1) (evalOpB Ab vars x2))  
  | Ab vars (invOL x1) := ((inv Ab) (evalOpB Ab vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((AbelianGroup A) → ((vector A n) → ((OpAbelianGroupTerm2 n A) → A))) 
  | Ab vars (v2 x1) := (nth vars x1)  
  | Ab vars (sing2 x1) := x1  
  | Ab vars oneOL2 := (one Ab)  
  | Ab vars (timesOL2 x1 x2) := ((times Ab) (evalOp Ab vars x1) (evalOp Ab vars x2))  
  | Ab vars (invOL2 x1) := ((inv Ab) (evalOp Ab vars x1))  
  def inductionB   (P : (AbelianGroupTerm → Type))  : ((P oneL) → ((∀ (x1 x2 : AbelianGroupTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 : AbelianGroupTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : AbelianGroupTerm) , (P x))))) 
  | p1l ptimesl pinvl oneL := p1l  
  | p1l ptimesl pinvl (timesL x1 x2) := (ptimesl _ _ (inductionB p1l ptimesl pinvl x1) (inductionB p1l ptimesl pinvl x2))  
  | p1l ptimesl pinvl (invL x1) := (pinvl _ (inductionB p1l ptimesl pinvl x1))  
  def inductionCl   (A : Type) (P : ((ClAbelianGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → ((∀ (x1 x2 : (ClAbelianGroupTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 : (ClAbelianGroupTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClAbelianGroupTerm A)) , (P x)))))) 
  | psing p1cl ptimescl pinvcl (sing x1) := (psing x1)  
  | psing p1cl ptimescl pinvcl oneCl := p1cl  
  | psing p1cl ptimescl pinvcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p1cl ptimescl pinvcl x1) (inductionCl psing p1cl ptimescl pinvcl x2))  
  | psing p1cl ptimescl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing p1cl ptimescl pinvcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpAbelianGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → ((∀ (x1 x2 : (OpAbelianGroupTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 : (OpAbelianGroupTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpAbelianGroupTerm n)) , (P x)))))) 
  | pv p1ol ptimesol pinvol (v x1) := (pv x1)  
  | pv p1ol ptimesol pinvol oneOL := p1ol  
  | pv p1ol ptimesol pinvol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p1ol ptimesol pinvol x1) (inductionOpB pv p1ol ptimesol pinvol x2))  
  | pv p1ol ptimesol pinvol (invOL x1) := (pinvol _ (inductionOpB pv p1ol ptimesol pinvol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAbelianGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → ((∀ (x1 x2 : (OpAbelianGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 : (OpAbelianGroupTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpAbelianGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 p1ol2 ptimesol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 ptimesol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 ptimesol2 pinvol2 oneOL2 := p1ol2  
  | pv2 psing2 p1ol2 ptimesol2 pinvol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p1ol2 ptimesol2 pinvol2 x1) (inductionOp pv2 psing2 p1ol2 ptimesol2 pinvol2 x2))  
  | pv2 psing2 p1ol2 ptimesol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 p1ol2 ptimesol2 pinvol2 x1))  
  def stageB  : (AbelianGroupTerm → (Staged AbelianGroupTerm))
  | oneL := (Now oneL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClAbelianGroupTerm A) → (Staged (ClAbelianGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpAbelianGroupTerm n) → (Staged (OpAbelianGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAbelianGroupTerm2 n A) → (Staged (OpAbelianGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (invT : ((Repr A) → (Repr A))) 
  
end AbelianGroup