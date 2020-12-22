import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedInvolutiveMagma0Sig   
  structure PointedInvolutiveMagma0Sig  (A : Type) : Type := 
       (times : (A → (A → A)))
       (prim : (A → A))
       (zero : A) 
  
  open PointedInvolutiveMagma0Sig
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (primS : (AS → AS))
       (zeroS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (zeroP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedInvolutiveMagma0Sig A1)) (Po2 : (PointedInvolutiveMagma0Sig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Po1) x1 x2)) = ((times Po2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Po1) x1)) = ((prim Po2) (hom x1))))
       (pres_zero : (hom (zero Po1)) = (zero Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedInvolutiveMagma0Sig A1)) (Po2 : (PointedInvolutiveMagma0Sig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Po1) x1 x2) ((times Po2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Po1) x1) ((prim Po2) y1)))))
       (interp_zero : (interp (zero Po1) (zero Po2))) 
  
  inductive PointedInvolutiveMagma0SigTerm   : Type  
     | timesL : (PointedInvolutiveMagma0SigTerm → (PointedInvolutiveMagma0SigTerm → PointedInvolutiveMagma0SigTerm)) 
     | primL : (PointedInvolutiveMagma0SigTerm → PointedInvolutiveMagma0SigTerm) 
     | zeroL : PointedInvolutiveMagma0SigTerm  
      open PointedInvolutiveMagma0SigTerm 
  
  inductive ClPointedInvolutiveMagma0SigTerm  (A : Type) : Type  
     | sing : (A → ClPointedInvolutiveMagma0SigTerm) 
     | timesCl : (ClPointedInvolutiveMagma0SigTerm → (ClPointedInvolutiveMagma0SigTerm → ClPointedInvolutiveMagma0SigTerm)) 
     | primCl : (ClPointedInvolutiveMagma0SigTerm → ClPointedInvolutiveMagma0SigTerm) 
     | zeroCl : ClPointedInvolutiveMagma0SigTerm  
      open ClPointedInvolutiveMagma0SigTerm 
  
  inductive OpPointedInvolutiveMagma0SigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedInvolutiveMagma0SigTerm) 
     | timesOL : (OpPointedInvolutiveMagma0SigTerm → (OpPointedInvolutiveMagma0SigTerm → OpPointedInvolutiveMagma0SigTerm)) 
     | primOL : (OpPointedInvolutiveMagma0SigTerm → OpPointedInvolutiveMagma0SigTerm) 
     | zeroOL : OpPointedInvolutiveMagma0SigTerm  
      open OpPointedInvolutiveMagma0SigTerm 
  
  inductive OpPointedInvolutiveMagma0SigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedInvolutiveMagma0SigTerm2) 
     | sing2 : (A → OpPointedInvolutiveMagma0SigTerm2) 
     | timesOL2 : (OpPointedInvolutiveMagma0SigTerm2 → (OpPointedInvolutiveMagma0SigTerm2 → OpPointedInvolutiveMagma0SigTerm2)) 
     | primOL2 : (OpPointedInvolutiveMagma0SigTerm2 → OpPointedInvolutiveMagma0SigTerm2) 
     | zeroOL2 : OpPointedInvolutiveMagma0SigTerm2  
      open OpPointedInvolutiveMagma0SigTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointedInvolutiveMagma0SigTerm A) → (ClPointedInvolutiveMagma0SigTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | zeroCl := zeroCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointedInvolutiveMagma0SigTerm n) → (OpPointedInvolutiveMagma0SigTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | zeroOL := zeroOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointedInvolutiveMagma0SigTerm2 n A) → (OpPointedInvolutiveMagma0SigTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | zeroOL2 := zeroOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedInvolutiveMagma0Sig A) → (PointedInvolutiveMagma0SigTerm → A)) 
  | Po (timesL x1 x2) := ((times Po) (evalB Po x1) (evalB Po x2))  
  | Po (primL x1) := ((prim Po) (evalB Po x1))  
  | Po zeroL := (zero Po)  
  def evalCl   {A : Type}  : ((PointedInvolutiveMagma0Sig A) → ((ClPointedInvolutiveMagma0SigTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po (timesCl x1 x2) := ((times Po) (evalCl Po x1) (evalCl Po x2))  
  | Po (primCl x1) := ((prim Po) (evalCl Po x1))  
  | Po zeroCl := (zero Po)  
  def evalOpB   {A : Type} (n : ℕ)  : ((PointedInvolutiveMagma0Sig A) → ((vector A n) → ((OpPointedInvolutiveMagma0SigTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars (timesOL x1 x2) := ((times Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  | Po vars (primOL x1) := ((prim Po) (evalOpB Po vars x1))  
  | Po vars zeroOL := (zero Po)  
  def evalOp   {A : Type} (n : ℕ)  : ((PointedInvolutiveMagma0Sig A) → ((vector A n) → ((OpPointedInvolutiveMagma0SigTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars (timesOL2 x1 x2) := ((times Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  | Po vars (primOL2 x1) := ((prim Po) (evalOp Po vars x1))  
  | Po vars zeroOL2 := (zero Po)  
  def inductionB   (P : (PointedInvolutiveMagma0SigTerm → Type))  : ((∀ (x1 x2 : PointedInvolutiveMagma0SigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 : PointedInvolutiveMagma0SigTerm) , ((P x1) → (P (primL x1)))) → ((P zeroL) → (∀ (x : PointedInvolutiveMagma0SigTerm) , (P x))))) 
  | ptimesl ppriml p0l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl ppriml p0l x1) (inductionB ptimesl ppriml p0l x2))  
  | ptimesl ppriml p0l (primL x1) := (ppriml _ (inductionB ptimesl ppriml p0l x1))  
  | ptimesl ppriml p0l zeroL := p0l  
  def inductionCl   (A : Type) (P : ((ClPointedInvolutiveMagma0SigTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPointedInvolutiveMagma0SigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 : (ClPointedInvolutiveMagma0SigTerm A)) , ((P x1) → (P (primCl x1)))) → ((P zeroCl) → (∀ (x : (ClPointedInvolutiveMagma0SigTerm A)) , (P x)))))) 
  | psing ptimescl pprimcl p0cl (sing x1) := (psing x1)  
  | psing ptimescl pprimcl p0cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl pprimcl p0cl x1) (inductionCl psing ptimescl pprimcl p0cl x2))  
  | psing ptimescl pprimcl p0cl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl pprimcl p0cl x1))  
  | psing ptimescl pprimcl p0cl zeroCl := p0cl  
  def inductionOpB   (n : ℕ) (P : ((OpPointedInvolutiveMagma0SigTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPointedInvolutiveMagma0SigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 : (OpPointedInvolutiveMagma0SigTerm n)) , ((P x1) → (P (primOL x1)))) → ((P zeroOL) → (∀ (x : (OpPointedInvolutiveMagma0SigTerm n)) , (P x)))))) 
  | pv ptimesol pprimol p0ol (v x1) := (pv x1)  
  | pv ptimesol pprimol p0ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pprimol p0ol x1) (inductionOpB pv ptimesol pprimol p0ol x2))  
  | pv ptimesol pprimol p0ol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pprimol p0ol x1))  
  | pv ptimesol pprimol p0ol zeroOL := p0ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointedInvolutiveMagma0SigTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPointedInvolutiveMagma0SigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 : (OpPointedInvolutiveMagma0SigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P zeroOL2) → (∀ (x : (OpPointedInvolutiveMagma0SigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pprimol2 p0ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pprimol2 p0ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pprimol2 p0ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pprimol2 p0ol2 x1) (inductionOp pv2 psing2 ptimesol2 pprimol2 p0ol2 x2))  
  | pv2 psing2 ptimesol2 pprimol2 p0ol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pprimol2 p0ol2 x1))  
  | pv2 psing2 ptimesol2 pprimol2 p0ol2 zeroOL2 := p0ol2  
  def stageB  : (PointedInvolutiveMagma0SigTerm → (Staged PointedInvolutiveMagma0SigTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | zeroL := (Now zeroL)  
  def stageCl   (A : Type)  : ((ClPointedInvolutiveMagma0SigTerm A) → (Staged (ClPointedInvolutiveMagma0SigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | zeroCl := (Now zeroCl)  
  def stageOpB   (n : ℕ)  : ((OpPointedInvolutiveMagma0SigTerm n) → (Staged (OpPointedInvolutiveMagma0SigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | zeroOL := (Now zeroOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointedInvolutiveMagma0SigTerm2 n A) → (Staged (OpPointedInvolutiveMagma0SigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | zeroOL2 := (Now zeroOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A)))
       (zeroT : (Repr A)) 
  
end PointedInvolutiveMagma0Sig