import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PrimRingoidSig   
  structure PrimRingoidSig  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (prim : (A → A)) 
  
  open PrimRingoidSig
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Pr1 : (PrimRingoidSig A1)) (Pr2 : (PrimRingoidSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Pr1) x1 x2)) = ((times Pr2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Pr1) x1 x2)) = ((plus Pr2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Pr1) x1)) = ((prim Pr2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Pr1 : (PrimRingoidSig A1)) (Pr2 : (PrimRingoidSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Pr1) x1 x2) ((times Pr2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Pr1) x1 x2) ((plus Pr2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Pr1) x1) ((prim Pr2) y1))))) 
  
  inductive PrimRingoidSigTerm   : Type  
     | timesL : (PrimRingoidSigTerm → (PrimRingoidSigTerm → PrimRingoidSigTerm)) 
     | plusL : (PrimRingoidSigTerm → (PrimRingoidSigTerm → PrimRingoidSigTerm)) 
     | primL : (PrimRingoidSigTerm → PrimRingoidSigTerm)  
      open PrimRingoidSigTerm 
  
  inductive ClPrimRingoidSigTerm  (A : Type) : Type  
     | sing : (A → ClPrimRingoidSigTerm) 
     | timesCl : (ClPrimRingoidSigTerm → (ClPrimRingoidSigTerm → ClPrimRingoidSigTerm)) 
     | plusCl : (ClPrimRingoidSigTerm → (ClPrimRingoidSigTerm → ClPrimRingoidSigTerm)) 
     | primCl : (ClPrimRingoidSigTerm → ClPrimRingoidSigTerm)  
      open ClPrimRingoidSigTerm 
  
  inductive OpPrimRingoidSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPrimRingoidSigTerm) 
     | timesOL : (OpPrimRingoidSigTerm → (OpPrimRingoidSigTerm → OpPrimRingoidSigTerm)) 
     | plusOL : (OpPrimRingoidSigTerm → (OpPrimRingoidSigTerm → OpPrimRingoidSigTerm)) 
     | primOL : (OpPrimRingoidSigTerm → OpPrimRingoidSigTerm)  
      open OpPrimRingoidSigTerm 
  
  inductive OpPrimRingoidSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPrimRingoidSigTerm2) 
     | sing2 : (A → OpPrimRingoidSigTerm2) 
     | timesOL2 : (OpPrimRingoidSigTerm2 → (OpPrimRingoidSigTerm2 → OpPrimRingoidSigTerm2)) 
     | plusOL2 : (OpPrimRingoidSigTerm2 → (OpPrimRingoidSigTerm2 → OpPrimRingoidSigTerm2)) 
     | primOL2 : (OpPrimRingoidSigTerm2 → OpPrimRingoidSigTerm2)  
      open OpPrimRingoidSigTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPrimRingoidSigTerm A) → (ClPrimRingoidSigTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPrimRingoidSigTerm n) → (OpPrimRingoidSigTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPrimRingoidSigTerm2 n A) → (OpPrimRingoidSigTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PrimRingoidSig A) → (PrimRingoidSigTerm → A)) 
  | Pr (timesL x1 x2) := ((times Pr) (evalB Pr x1) (evalB Pr x2))  
  | Pr (plusL x1 x2) := ((plus Pr) (evalB Pr x1) (evalB Pr x2))  
  | Pr (primL x1) := ((prim Pr) (evalB Pr x1))  
  def evalCl   {A : Type}  : ((PrimRingoidSig A) → ((ClPrimRingoidSigTerm A) → A)) 
  | Pr (sing x1) := x1  
  | Pr (timesCl x1 x2) := ((times Pr) (evalCl Pr x1) (evalCl Pr x2))  
  | Pr (plusCl x1 x2) := ((plus Pr) (evalCl Pr x1) (evalCl Pr x2))  
  | Pr (primCl x1) := ((prim Pr) (evalCl Pr x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((PrimRingoidSig A) → ((vector A n) → ((OpPrimRingoidSigTerm n) → A))) 
  | Pr vars (v x1) := (nth vars x1)  
  | Pr vars (timesOL x1 x2) := ((times Pr) (evalOpB Pr vars x1) (evalOpB Pr vars x2))  
  | Pr vars (plusOL x1 x2) := ((plus Pr) (evalOpB Pr vars x1) (evalOpB Pr vars x2))  
  | Pr vars (primOL x1) := ((prim Pr) (evalOpB Pr vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((PrimRingoidSig A) → ((vector A n) → ((OpPrimRingoidSigTerm2 n A) → A))) 
  | Pr vars (v2 x1) := (nth vars x1)  
  | Pr vars (sing2 x1) := x1  
  | Pr vars (timesOL2 x1 x2) := ((times Pr) (evalOp Pr vars x1) (evalOp Pr vars x2))  
  | Pr vars (plusOL2 x1 x2) := ((plus Pr) (evalOp Pr vars x1) (evalOp Pr vars x2))  
  | Pr vars (primOL2 x1) := ((prim Pr) (evalOp Pr vars x1))  
  def inductionB   (P : (PrimRingoidSigTerm → Type))  : ((∀ (x1 x2 : PrimRingoidSigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : PrimRingoidSigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : PrimRingoidSigTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : PrimRingoidSigTerm) , (P x))))) 
  | ptimesl pplusl ppriml (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (primL x1) := (ppriml _ (inductionB ptimesl pplusl ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClPrimRingoidSigTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPrimRingoidSigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClPrimRingoidSigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClPrimRingoidSigTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClPrimRingoidSigTerm A)) , (P x)))))) 
  | psing ptimescl ppluscl pprimcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl pprimcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl ppluscl pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpPrimRingoidSigTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPrimRingoidSigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpPrimRingoidSigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpPrimRingoidSigTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpPrimRingoidSigTerm n)) , (P x)))))) 
  | pv ptimesol pplusol pprimol (v x1) := (pv x1)  
  | pv ptimesol pplusol pprimol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pplusol pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPrimRingoidSigTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPrimRingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpPrimRingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpPrimRingoidSigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpPrimRingoidSigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1))  
  def stageB  : (PrimRingoidSigTerm → (Staged PrimRingoidSigTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClPrimRingoidSigTerm A) → (Staged (ClPrimRingoidSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpPrimRingoidSigTerm n) → (Staged (OpPrimRingoidSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPrimRingoidSigTerm2 n A) → (Staged (OpPrimRingoidSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end PrimRingoidSig