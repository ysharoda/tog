import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultUnaryAntiDistribution   
  structure MultUnaryAntiDistribution  (A : Type) : Type := 
       (prim : (A → A))
       (times : (A → (A → A)))
       (antidis_prim_times : (∀ {x y : A} , (prim (times x y)) = (times (prim y) (prim x)))) 
  
  open MultUnaryAntiDistribution
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (antidis_prim_timesP : (∀ {xP yP : (Prod A A)} , (primP (timesP xP yP)) = (timesP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultUnaryAntiDistribution A1)) (Mu2 : (MultUnaryAntiDistribution A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Mu1) x1)) = ((prim Mu2) (hom x1))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultUnaryAntiDistribution A1)) (Mu2 : (MultUnaryAntiDistribution A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Mu1) x1) ((prim Mu2) y1)))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2)))))) 
  
  inductive MultUnaryAntiDistributionTerm   : Type  
     | primL : (MultUnaryAntiDistributionTerm → MultUnaryAntiDistributionTerm) 
     | timesL : (MultUnaryAntiDistributionTerm → (MultUnaryAntiDistributionTerm → MultUnaryAntiDistributionTerm))  
      open MultUnaryAntiDistributionTerm 
  
  inductive ClMultUnaryAntiDistributionTerm  (A : Type) : Type  
     | sing : (A → ClMultUnaryAntiDistributionTerm) 
     | primCl : (ClMultUnaryAntiDistributionTerm → ClMultUnaryAntiDistributionTerm) 
     | timesCl : (ClMultUnaryAntiDistributionTerm → (ClMultUnaryAntiDistributionTerm → ClMultUnaryAntiDistributionTerm))  
      open ClMultUnaryAntiDistributionTerm 
  
  inductive OpMultUnaryAntiDistributionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultUnaryAntiDistributionTerm) 
     | primOL : (OpMultUnaryAntiDistributionTerm → OpMultUnaryAntiDistributionTerm) 
     | timesOL : (OpMultUnaryAntiDistributionTerm → (OpMultUnaryAntiDistributionTerm → OpMultUnaryAntiDistributionTerm))  
      open OpMultUnaryAntiDistributionTerm 
  
  inductive OpMultUnaryAntiDistributionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultUnaryAntiDistributionTerm2) 
     | sing2 : (A → OpMultUnaryAntiDistributionTerm2) 
     | primOL2 : (OpMultUnaryAntiDistributionTerm2 → OpMultUnaryAntiDistributionTerm2) 
     | timesOL2 : (OpMultUnaryAntiDistributionTerm2 → (OpMultUnaryAntiDistributionTerm2 → OpMultUnaryAntiDistributionTerm2))  
      open OpMultUnaryAntiDistributionTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMultUnaryAntiDistributionTerm A) → (ClMultUnaryAntiDistributionTerm A)) 
  | (timesCl (primCl y) (primCl x)) := (primCl (timesCl x y))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMultUnaryAntiDistributionTerm n) → (OpMultUnaryAntiDistributionTerm n)) 
  | (timesOL (primOL y) (primOL x)) := (primOL (timesOL x y))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMultUnaryAntiDistributionTerm2 n A) → (OpMultUnaryAntiDistributionTerm2 n A)) 
  | (timesOL2 (primOL2 y) (primOL2 x)) := (primOL2 (timesOL2 x y))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultUnaryAntiDistribution A) → (MultUnaryAntiDistributionTerm → A)) 
  | Mu (primL x1) := ((prim Mu) (evalB Mu x1))  
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  def evalCl   {A : Type}  : ((MultUnaryAntiDistribution A) → ((ClMultUnaryAntiDistributionTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu (primCl x1) := ((prim Mu) (evalCl Mu x1))  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MultUnaryAntiDistribution A) → ((vector A n) → ((OpMultUnaryAntiDistributionTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars (primOL x1) := ((prim Mu) (evalOpB Mu vars x1))  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((MultUnaryAntiDistribution A) → ((vector A n) → ((OpMultUnaryAntiDistributionTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars (primOL2 x1) := ((prim Mu) (evalOp Mu vars x1))  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  def inductionB   (P : (MultUnaryAntiDistributionTerm → Type))  : ((∀ (x1 : MultUnaryAntiDistributionTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : MultUnaryAntiDistributionTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : MultUnaryAntiDistributionTerm) , (P x)))) 
  | ppriml ptimesl (primL x1) := (ppriml _ (inductionB ppriml ptimesl x1))  
  | ppriml ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB ppriml ptimesl x1) (inductionB ppriml ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClMultUnaryAntiDistributionTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClMultUnaryAntiDistributionTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClMultUnaryAntiDistributionTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClMultUnaryAntiDistributionTerm A)) , (P x))))) 
  | psing pprimcl ptimescl (sing x1) := (psing x1)  
  | psing pprimcl ptimescl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl ptimescl x1))  
  | psing pprimcl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing pprimcl ptimescl x1) (inductionCl psing pprimcl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpMultUnaryAntiDistributionTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpMultUnaryAntiDistributionTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpMultUnaryAntiDistributionTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpMultUnaryAntiDistributionTerm n)) , (P x))))) 
  | pv pprimol ptimesol (v x1) := (pv x1)  
  | pv pprimol ptimesol (primOL x1) := (pprimol _ (inductionOpB pv pprimol ptimesol x1))  
  | pv pprimol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pprimol ptimesol x1) (inductionOpB pv pprimol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMultUnaryAntiDistributionTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpMultUnaryAntiDistributionTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpMultUnaryAntiDistributionTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpMultUnaryAntiDistributionTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 ptimesol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 ptimesol2 x1))  
  | pv2 psing2 pprimol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pprimol2 ptimesol2 x1) (inductionOp pv2 psing2 pprimol2 ptimesol2 x2))  
  def stageB  : (MultUnaryAntiDistributionTerm → (Staged MultUnaryAntiDistributionTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClMultUnaryAntiDistributionTerm A) → (Staged (ClMultUnaryAntiDistributionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpMultUnaryAntiDistributionTerm n) → (Staged (OpMultUnaryAntiDistributionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMultUnaryAntiDistributionTerm2 n A) → (Staged (OpMultUnaryAntiDistributionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MultUnaryAntiDistribution