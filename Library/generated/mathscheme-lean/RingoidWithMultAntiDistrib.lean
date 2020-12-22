import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RingoidWithMultAntiDistrib   
  structure RingoidWithMultAntiDistrib  (A : Type) : Type := 
       (times : (A → (A → A)))
       (prim : (A → A))
       (antidis_prim_times : (∀ {x y : A} , (prim (times x y)) = (times (prim y) (prim x))))
       (plus : (A → (A → A)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open RingoidWithMultAntiDistrib
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (primS : (AS → AS))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (antidis_prim_timesP : (∀ {xP yP : (Prod A A)} , (primP (timesP xP yP)) = (timesP (primP yP) (primP xP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RingoidWithMultAntiDistrib A1)) (Ri2 : (RingoidWithMultAntiDistrib A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Ri1) x1)) = ((prim Ri2) (hom x1))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RingoidWithMultAntiDistrib A1)) (Ri2 : (RingoidWithMultAntiDistrib A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Ri1) x1) ((prim Ri2) y1)))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2)))))) 
  
  inductive RingoidWithMultAntiDistribTerm   : Type  
     | timesL : (RingoidWithMultAntiDistribTerm → (RingoidWithMultAntiDistribTerm → RingoidWithMultAntiDistribTerm)) 
     | primL : (RingoidWithMultAntiDistribTerm → RingoidWithMultAntiDistribTerm) 
     | plusL : (RingoidWithMultAntiDistribTerm → (RingoidWithMultAntiDistribTerm → RingoidWithMultAntiDistribTerm))  
      open RingoidWithMultAntiDistribTerm 
  
  inductive ClRingoidWithMultAntiDistribTerm  (A : Type) : Type  
     | sing : (A → ClRingoidWithMultAntiDistribTerm) 
     | timesCl : (ClRingoidWithMultAntiDistribTerm → (ClRingoidWithMultAntiDistribTerm → ClRingoidWithMultAntiDistribTerm)) 
     | primCl : (ClRingoidWithMultAntiDistribTerm → ClRingoidWithMultAntiDistribTerm) 
     | plusCl : (ClRingoidWithMultAntiDistribTerm → (ClRingoidWithMultAntiDistribTerm → ClRingoidWithMultAntiDistribTerm))  
      open ClRingoidWithMultAntiDistribTerm 
  
  inductive OpRingoidWithMultAntiDistribTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoidWithMultAntiDistribTerm) 
     | timesOL : (OpRingoidWithMultAntiDistribTerm → (OpRingoidWithMultAntiDistribTerm → OpRingoidWithMultAntiDistribTerm)) 
     | primOL : (OpRingoidWithMultAntiDistribTerm → OpRingoidWithMultAntiDistribTerm) 
     | plusOL : (OpRingoidWithMultAntiDistribTerm → (OpRingoidWithMultAntiDistribTerm → OpRingoidWithMultAntiDistribTerm))  
      open OpRingoidWithMultAntiDistribTerm 
  
  inductive OpRingoidWithMultAntiDistribTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoidWithMultAntiDistribTerm2) 
     | sing2 : (A → OpRingoidWithMultAntiDistribTerm2) 
     | timesOL2 : (OpRingoidWithMultAntiDistribTerm2 → (OpRingoidWithMultAntiDistribTerm2 → OpRingoidWithMultAntiDistribTerm2)) 
     | primOL2 : (OpRingoidWithMultAntiDistribTerm2 → OpRingoidWithMultAntiDistribTerm2) 
     | plusOL2 : (OpRingoidWithMultAntiDistribTerm2 → (OpRingoidWithMultAntiDistribTerm2 → OpRingoidWithMultAntiDistribTerm2))  
      open OpRingoidWithMultAntiDistribTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRingoidWithMultAntiDistribTerm A) → (ClRingoidWithMultAntiDistribTerm A)) 
  | (timesCl (primCl y) (primCl x)) := (primCl (timesCl x y))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRingoidWithMultAntiDistribTerm n) → (OpRingoidWithMultAntiDistribTerm n)) 
  | (timesOL (primOL y) (primOL x)) := (primOL (timesOL x y))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRingoidWithMultAntiDistribTerm2 n A) → (OpRingoidWithMultAntiDistribTerm2 n A)) 
  | (timesOL2 (primOL2 y) (primOL2 x)) := (primOL2 (timesOL2 x y))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RingoidWithMultAntiDistrib A) → (RingoidWithMultAntiDistribTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (primL x1) := ((prim Ri) (evalB Ri x1))  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RingoidWithMultAntiDistrib A) → ((ClRingoidWithMultAntiDistribTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (primCl x1) := ((prim Ri) (evalCl Ri x1))  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((RingoidWithMultAntiDistrib A) → ((vector A n) → ((OpRingoidWithMultAntiDistribTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (primOL x1) := ((prim Ri) (evalOpB Ri vars x1))  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((RingoidWithMultAntiDistrib A) → ((vector A n) → ((OpRingoidWithMultAntiDistribTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (primOL2 x1) := ((prim Ri) (evalOp Ri vars x1))  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   (P : (RingoidWithMultAntiDistribTerm → Type))  : ((∀ (x1 x2 : RingoidWithMultAntiDistribTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 : RingoidWithMultAntiDistribTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : RingoidWithMultAntiDistribTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : RingoidWithMultAntiDistribTerm) , (P x))))) 
  | ptimesl ppriml pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl ppriml pplusl x1) (inductionB ptimesl ppriml pplusl x2))  
  | ptimesl ppriml pplusl (primL x1) := (ppriml _ (inductionB ptimesl ppriml pplusl x1))  
  | ptimesl ppriml pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl ppriml pplusl x1) (inductionB ptimesl ppriml pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClRingoidWithMultAntiDistribTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingoidWithMultAntiDistribTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 : (ClRingoidWithMultAntiDistribTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClRingoidWithMultAntiDistribTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClRingoidWithMultAntiDistribTerm A)) , (P x)))))) 
  | psing ptimescl pprimcl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl pprimcl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl pprimcl ppluscl x1) (inductionCl psing ptimescl pprimcl ppluscl x2))  
  | psing ptimescl pprimcl ppluscl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl pprimcl ppluscl x1))  
  | psing ptimescl pprimcl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl pprimcl ppluscl x1) (inductionCl psing ptimescl pprimcl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpRingoidWithMultAntiDistribTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingoidWithMultAntiDistribTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 : (OpRingoidWithMultAntiDistribTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpRingoidWithMultAntiDistribTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpRingoidWithMultAntiDistribTerm n)) , (P x)))))) 
  | pv ptimesol pprimol pplusol (v x1) := (pv x1)  
  | pv ptimesol pprimol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pprimol pplusol x1) (inductionOpB pv ptimesol pprimol pplusol x2))  
  | pv ptimesol pprimol pplusol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pprimol pplusol x1))  
  | pv ptimesol pprimol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pprimol pplusol x1) (inductionOpB pv ptimesol pprimol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRingoidWithMultAntiDistribTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingoidWithMultAntiDistribTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 : (OpRingoidWithMultAntiDistribTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpRingoidWithMultAntiDistribTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpRingoidWithMultAntiDistribTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pprimol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pprimol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pprimol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pprimol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pprimol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pprimol2 pplusol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pprimol2 pplusol2 x1))  
  | pv2 psing2 ptimesol2 pprimol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pprimol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pprimol2 pplusol2 x2))  
  def stageB  : (RingoidWithMultAntiDistribTerm → (Staged RingoidWithMultAntiDistribTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClRingoidWithMultAntiDistribTerm A) → (Staged (ClRingoidWithMultAntiDistribTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpRingoidWithMultAntiDistribTerm n) → (Staged (OpRingoidWithMultAntiDistribTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRingoidWithMultAntiDistribTerm2 n A) → (Staged (OpRingoidWithMultAntiDistribTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A)))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RingoidWithMultAntiDistrib