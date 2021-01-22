import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedTimesZeroMagma   
  structure PointedTimesZeroMagma  (A : Type) : Type := 
       (zero : A)
       (times : (A → (A → A))) 
  
  open PointedTimesZeroMagma
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedTimesZeroMagma A1)) (Po2 : (PointedTimesZeroMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Po1)) = (zero Po2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Po1) x1 x2)) = ((times Po2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedTimesZeroMagma A1)) (Po2 : (PointedTimesZeroMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Po1) (zero Po2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Po1) x1 x2) ((times Po2) y1 y2)))))) 
  
  inductive PointedTimesZeroMagmaTerm   : Type  
     | zeroL : PointedTimesZeroMagmaTerm 
     | timesL : (PointedTimesZeroMagmaTerm → (PointedTimesZeroMagmaTerm → PointedTimesZeroMagmaTerm))  
      open PointedTimesZeroMagmaTerm 
  
  inductive ClPointedTimesZeroMagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointedTimesZeroMagmaTerm) 
     | zeroCl : ClPointedTimesZeroMagmaTerm 
     | timesCl : (ClPointedTimesZeroMagmaTerm → (ClPointedTimesZeroMagmaTerm → ClPointedTimesZeroMagmaTerm))  
      open ClPointedTimesZeroMagmaTerm 
  
  inductive OpPointedTimesZeroMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedTimesZeroMagmaTerm) 
     | zeroOL : OpPointedTimesZeroMagmaTerm 
     | timesOL : (OpPointedTimesZeroMagmaTerm → (OpPointedTimesZeroMagmaTerm → OpPointedTimesZeroMagmaTerm))  
      open OpPointedTimesZeroMagmaTerm 
  
  inductive OpPointedTimesZeroMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedTimesZeroMagmaTerm2) 
     | sing2 : (A → OpPointedTimesZeroMagmaTerm2) 
     | zeroOL2 : OpPointedTimesZeroMagmaTerm2 
     | timesOL2 : (OpPointedTimesZeroMagmaTerm2 → (OpPointedTimesZeroMagmaTerm2 → OpPointedTimesZeroMagmaTerm2))  
      open OpPointedTimesZeroMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPointedTimesZeroMagmaTerm A) → (ClPointedTimesZeroMagmaTerm A)) 
  | zeroCl := zeroCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPointedTimesZeroMagmaTerm n) → (OpPointedTimesZeroMagmaTerm n)) 
  | zeroOL := zeroOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPointedTimesZeroMagmaTerm2 n A) → (OpPointedTimesZeroMagmaTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedTimesZeroMagma A) → (PointedTimesZeroMagmaTerm → A)) 
  | Po zeroL := (zero Po)  
  | Po (timesL x1 x2) := ((times Po) (evalB Po x1) (evalB Po x2))  
  def evalCl   {A : Type}  : ((PointedTimesZeroMagma A) → ((ClPointedTimesZeroMagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po zeroCl := (zero Po)  
  | Po (timesCl x1 x2) := ((times Po) (evalCl Po x1) (evalCl Po x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((PointedTimesZeroMagma A) → ((vector A n) → ((OpPointedTimesZeroMagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars zeroOL := (zero Po)  
  | Po vars (timesOL x1 x2) := ((times Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((PointedTimesZeroMagma A) → ((vector A n) → ((OpPointedTimesZeroMagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars zeroOL2 := (zero Po)  
  | Po vars (timesOL2 x1 x2) := ((times Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  def inductionB   {P : (PointedTimesZeroMagmaTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : PointedTimesZeroMagmaTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : PointedTimesZeroMagmaTerm) , (P x)))) 
  | p0l ptimesl zeroL := p0l  
  | p0l ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l ptimesl x1) (inductionB p0l ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClPointedTimesZeroMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClPointedTimesZeroMagmaTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClPointedTimesZeroMagmaTerm A)) , (P x))))) 
  | psing p0cl ptimescl (sing x1) := (psing x1)  
  | psing p0cl ptimescl zeroCl := p0cl  
  | psing p0cl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ptimescl x1) (inductionCl psing p0cl ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpPointedTimesZeroMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpPointedTimesZeroMagmaTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpPointedTimesZeroMagmaTerm n)) , (P x))))) 
  | pv p0ol ptimesol (v x1) := (pv x1)  
  | pv p0ol ptimesol zeroOL := p0ol  
  | pv p0ol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol ptimesol x1) (inductionOpB pv p0ol ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPointedTimesZeroMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpPointedTimesZeroMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpPointedTimesZeroMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 p0ol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 ptimesol2 x2))  
  def stageB  : (PointedTimesZeroMagmaTerm → (Staged PointedTimesZeroMagmaTerm))
  | zeroL := (Now zeroL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClPointedTimesZeroMagmaTerm A) → (Staged (ClPointedTimesZeroMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpPointedTimesZeroMagmaTerm n) → (Staged (OpPointedTimesZeroMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPointedTimesZeroMagmaTerm2 n A) → (Staged (OpPointedTimesZeroMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end PointedTimesZeroMagma