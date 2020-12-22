import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultGroup   
  structure MultGroup  (A : Type) : Type := 
       (times : (A → (A → A)))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (inv : (A → A))
       (leftInverse_inv_op_one : (∀ {x : A} , (times x (inv x)) = one))
       (rightInverse_inv_op_one : (∀ {x : A} , (times (inv x) x) = one)) 
  
  open MultGroup
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS)
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (invP : ((Prod A A) → (Prod A A)))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP xP (invP xP)) = oneP))
       (rightInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP (invP xP) xP) = oneP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultGroup A1)) (Mu2 : (MultGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2))))
       (pres_one : (hom (one Mu1)) = (one Mu2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Mu1) x1)) = ((inv Mu2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultGroup A1)) (Mu2 : (MultGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2))))))
       (interp_one : (interp (one Mu1) (one Mu2)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Mu1) x1) ((inv Mu2) y1))))) 
  
  inductive MultGroupTerm   : Type  
     | timesL : (MultGroupTerm → (MultGroupTerm → MultGroupTerm)) 
     | oneL : MultGroupTerm 
     | invL : (MultGroupTerm → MultGroupTerm)  
      open MultGroupTerm 
  
  inductive ClMultGroupTerm  (A : Type) : Type  
     | sing : (A → ClMultGroupTerm) 
     | timesCl : (ClMultGroupTerm → (ClMultGroupTerm → ClMultGroupTerm)) 
     | oneCl : ClMultGroupTerm 
     | invCl : (ClMultGroupTerm → ClMultGroupTerm)  
      open ClMultGroupTerm 
  
  inductive OpMultGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultGroupTerm) 
     | timesOL : (OpMultGroupTerm → (OpMultGroupTerm → OpMultGroupTerm)) 
     | oneOL : OpMultGroupTerm 
     | invOL : (OpMultGroupTerm → OpMultGroupTerm)  
      open OpMultGroupTerm 
  
  inductive OpMultGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultGroupTerm2) 
     | sing2 : (A → OpMultGroupTerm2) 
     | timesOL2 : (OpMultGroupTerm2 → (OpMultGroupTerm2 → OpMultGroupTerm2)) 
     | oneOL2 : OpMultGroupTerm2 
     | invOL2 : (OpMultGroupTerm2 → OpMultGroupTerm2)  
      open OpMultGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMultGroupTerm A) → (ClMultGroupTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMultGroupTerm n) → (OpMultGroupTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMultGroupTerm2 n A) → (OpMultGroupTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultGroup A) → (MultGroupTerm → A)) 
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  | Mu oneL := (one Mu)  
  | Mu (invL x1) := ((inv Mu) (evalB Mu x1))  
  def evalCl   {A : Type}  : ((MultGroup A) → ((ClMultGroupTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  | Mu oneCl := (one Mu)  
  | Mu (invCl x1) := ((inv Mu) (evalCl Mu x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MultGroup A) → ((vector A n) → ((OpMultGroupTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  | Mu vars oneOL := (one Mu)  
  | Mu vars (invOL x1) := ((inv Mu) (evalOpB Mu vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((MultGroup A) → ((vector A n) → ((OpMultGroupTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  | Mu vars oneOL2 := (one Mu)  
  | Mu vars (invOL2 x1) := ((inv Mu) (evalOp Mu vars x1))  
  def inductionB   (P : (MultGroupTerm → Type))  : ((∀ (x1 x2 : MultGroupTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → ((∀ (x1 : MultGroupTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : MultGroupTerm) , (P x))))) 
  | ptimesl p1l pinvl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l pinvl x1) (inductionB ptimesl p1l pinvl x2))  
  | ptimesl p1l pinvl oneL := p1l  
  | ptimesl p1l pinvl (invL x1) := (pinvl _ (inductionB ptimesl p1l pinvl x1))  
  def inductionCl   (A : Type) (P : ((ClMultGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMultGroupTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → ((∀ (x1 : (ClMultGroupTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClMultGroupTerm A)) , (P x)))))) 
  | psing ptimescl p1cl pinvcl (sing x1) := (psing x1)  
  | psing ptimescl p1cl pinvcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl pinvcl x1) (inductionCl psing ptimescl p1cl pinvcl x2))  
  | psing ptimescl p1cl pinvcl oneCl := p1cl  
  | psing ptimescl p1cl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing ptimescl p1cl pinvcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpMultGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMultGroupTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → ((∀ (x1 : (OpMultGroupTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpMultGroupTerm n)) , (P x)))))) 
  | pv ptimesol p1ol pinvol (v x1) := (pv x1)  
  | pv ptimesol p1ol pinvol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol pinvol x1) (inductionOpB pv ptimesol p1ol pinvol x2))  
  | pv ptimesol p1ol pinvol oneOL := p1ol  
  | pv ptimesol p1ol pinvol (invOL x1) := (pinvol _ (inductionOpB pv ptimesol p1ol pinvol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMultGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMultGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 : (OpMultGroupTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpMultGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 x1))  
  def stageB  : (MultGroupTerm → (Staged MultGroupTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClMultGroupTerm A) → (Staged (ClMultGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpMultGroupTerm n) → (Staged (OpMultGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMultGroupTerm2 n A) → (Staged (OpMultGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (invT : ((Repr A) → (Repr A))) 
  
end MultGroup