import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RingoidWithAddAntiDistrib   
  structure RingoidWithAddAntiDistrib  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (prim : (A → A))
       (antidis_prim_plus : (∀ {x y : A} , (prim (plus x y)) = (plus (prim y) (prim x))))
       (times : (A → (A → A)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open RingoidWithAddAntiDistrib
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (primS : (AS → AS))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (antidis_prim_plusP : (∀ {xP yP : (Prod A A)} , (primP (plusP xP yP)) = (plusP (primP yP) (primP xP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RingoidWithAddAntiDistrib A1)) (Ri2 : (RingoidWithAddAntiDistrib A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Ri1) x1)) = ((prim Ri2) (hom x1))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RingoidWithAddAntiDistrib A1)) (Ri2 : (RingoidWithAddAntiDistrib A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Ri1) x1) ((prim Ri2) y1)))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2)))))) 
  
  inductive RingoidWithAddAntiDistribTerm   : Type  
     | plusL : (RingoidWithAddAntiDistribTerm → (RingoidWithAddAntiDistribTerm → RingoidWithAddAntiDistribTerm)) 
     | primL : (RingoidWithAddAntiDistribTerm → RingoidWithAddAntiDistribTerm) 
     | timesL : (RingoidWithAddAntiDistribTerm → (RingoidWithAddAntiDistribTerm → RingoidWithAddAntiDistribTerm))  
      open RingoidWithAddAntiDistribTerm 
  
  inductive ClRingoidWithAddAntiDistribTerm  (A : Type) : Type  
     | sing : (A → ClRingoidWithAddAntiDistribTerm) 
     | plusCl : (ClRingoidWithAddAntiDistribTerm → (ClRingoidWithAddAntiDistribTerm → ClRingoidWithAddAntiDistribTerm)) 
     | primCl : (ClRingoidWithAddAntiDistribTerm → ClRingoidWithAddAntiDistribTerm) 
     | timesCl : (ClRingoidWithAddAntiDistribTerm → (ClRingoidWithAddAntiDistribTerm → ClRingoidWithAddAntiDistribTerm))  
      open ClRingoidWithAddAntiDistribTerm 
  
  inductive OpRingoidWithAddAntiDistribTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoidWithAddAntiDistribTerm) 
     | plusOL : (OpRingoidWithAddAntiDistribTerm → (OpRingoidWithAddAntiDistribTerm → OpRingoidWithAddAntiDistribTerm)) 
     | primOL : (OpRingoidWithAddAntiDistribTerm → OpRingoidWithAddAntiDistribTerm) 
     | timesOL : (OpRingoidWithAddAntiDistribTerm → (OpRingoidWithAddAntiDistribTerm → OpRingoidWithAddAntiDistribTerm))  
      open OpRingoidWithAddAntiDistribTerm 
  
  inductive OpRingoidWithAddAntiDistribTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoidWithAddAntiDistribTerm2) 
     | sing2 : (A → OpRingoidWithAddAntiDistribTerm2) 
     | plusOL2 : (OpRingoidWithAddAntiDistribTerm2 → (OpRingoidWithAddAntiDistribTerm2 → OpRingoidWithAddAntiDistribTerm2)) 
     | primOL2 : (OpRingoidWithAddAntiDistribTerm2 → OpRingoidWithAddAntiDistribTerm2) 
     | timesOL2 : (OpRingoidWithAddAntiDistribTerm2 → (OpRingoidWithAddAntiDistribTerm2 → OpRingoidWithAddAntiDistribTerm2))  
      open OpRingoidWithAddAntiDistribTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRingoidWithAddAntiDistribTerm A) → (ClRingoidWithAddAntiDistribTerm A)) 
  | (plusCl (primCl y) (primCl x)) := (primCl (plusCl x y))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRingoidWithAddAntiDistribTerm n) → (OpRingoidWithAddAntiDistribTerm n)) 
  | (plusOL (primOL y) (primOL x)) := (primOL (plusOL x y))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRingoidWithAddAntiDistribTerm2 n A) → (OpRingoidWithAddAntiDistribTerm2 n A)) 
  | (plusOL2 (primOL2 y) (primOL2 x)) := (primOL2 (plusOL2 x y))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RingoidWithAddAntiDistrib A) → (RingoidWithAddAntiDistribTerm → A)) 
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (primL x1) := ((prim Ri) (evalB Ri x1))  
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RingoidWithAddAntiDistrib A) → ((ClRingoidWithAddAntiDistribTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (primCl x1) := ((prim Ri) (evalCl Ri x1))  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((RingoidWithAddAntiDistrib A) → ((vector A n) → ((OpRingoidWithAddAntiDistribTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (primOL x1) := ((prim Ri) (evalOpB Ri vars x1))  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((RingoidWithAddAntiDistrib A) → ((vector A n) → ((OpRingoidWithAddAntiDistribTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (primOL2 x1) := ((prim Ri) (evalOp Ri vars x1))  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   (P : (RingoidWithAddAntiDistribTerm → Type))  : ((∀ (x1 x2 : RingoidWithAddAntiDistribTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : RingoidWithAddAntiDistribTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : RingoidWithAddAntiDistribTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : RingoidWithAddAntiDistribTerm) , (P x))))) 
  | pplusl ppriml ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl ppriml ptimesl x1) (inductionB pplusl ppriml ptimesl x2))  
  | pplusl ppriml ptimesl (primL x1) := (ppriml _ (inductionB pplusl ppriml ptimesl x1))  
  | pplusl ppriml ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl ppriml ptimesl x1) (inductionB pplusl ppriml ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClRingoidWithAddAntiDistribTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingoidWithAddAntiDistribTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClRingoidWithAddAntiDistribTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClRingoidWithAddAntiDistribTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClRingoidWithAddAntiDistribTerm A)) , (P x)))))) 
  | psing ppluscl pprimcl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl pprimcl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl pprimcl ptimescl x1) (inductionCl psing ppluscl pprimcl ptimescl x2))  
  | psing ppluscl pprimcl ptimescl (primCl x1) := (pprimcl _ (inductionCl psing ppluscl pprimcl ptimescl x1))  
  | psing ppluscl pprimcl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl pprimcl ptimescl x1) (inductionCl psing ppluscl pprimcl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpRingoidWithAddAntiDistribTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingoidWithAddAntiDistribTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpRingoidWithAddAntiDistribTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpRingoidWithAddAntiDistribTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpRingoidWithAddAntiDistribTerm n)) , (P x)))))) 
  | pv pplusol pprimol ptimesol (v x1) := (pv x1)  
  | pv pplusol pprimol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol pprimol ptimesol x1) (inductionOpB pv pplusol pprimol ptimesol x2))  
  | pv pplusol pprimol ptimesol (primOL x1) := (pprimol _ (inductionOpB pv pplusol pprimol ptimesol x1))  
  | pv pplusol pprimol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol pprimol ptimesol x1) (inductionOpB pv pplusol pprimol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRingoidWithAddAntiDistribTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingoidWithAddAntiDistribTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpRingoidWithAddAntiDistribTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpRingoidWithAddAntiDistribTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpRingoidWithAddAntiDistribTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pplusol2 pprimol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 pprimol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 pprimol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 pprimol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 pprimol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 pprimol2 ptimesol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pplusol2 pprimol2 ptimesol2 x1))  
  | pv2 psing2 pplusol2 pprimol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 pprimol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 pprimol2 ptimesol2 x2))  
  def stageB  : (RingoidWithAddAntiDistribTerm → (Staged RingoidWithAddAntiDistribTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClRingoidWithAddAntiDistribTerm A) → (Staged (ClRingoidWithAddAntiDistribTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpRingoidWithAddAntiDistribTerm n) → (Staged (OpRingoidWithAddAntiDistribTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRingoidWithAddAntiDistribTerm2 n A) → (Staged (OpRingoidWithAddAntiDistribTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A)))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RingoidWithAddAntiDistrib