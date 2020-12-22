import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RingoidWithInvolution   
  structure RingoidWithInvolution  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (prim : (A → A)) 
  
  open RingoidWithInvolution
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RingoidWithInvolution A1)) (Ri2 : (RingoidWithInvolution A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Ri1) x1)) = ((prim Ri2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RingoidWithInvolution A1)) (Ri2 : (RingoidWithInvolution A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Ri1) x1) ((prim Ri2) y1))))) 
  
  inductive RingoidWithInvolutionTerm   : Type  
     | timesL : (RingoidWithInvolutionTerm → (RingoidWithInvolutionTerm → RingoidWithInvolutionTerm)) 
     | plusL : (RingoidWithInvolutionTerm → (RingoidWithInvolutionTerm → RingoidWithInvolutionTerm)) 
     | primL : (RingoidWithInvolutionTerm → RingoidWithInvolutionTerm)  
      open RingoidWithInvolutionTerm 
  
  inductive ClRingoidWithInvolutionTerm  (A : Type) : Type  
     | sing : (A → ClRingoidWithInvolutionTerm) 
     | timesCl : (ClRingoidWithInvolutionTerm → (ClRingoidWithInvolutionTerm → ClRingoidWithInvolutionTerm)) 
     | plusCl : (ClRingoidWithInvolutionTerm → (ClRingoidWithInvolutionTerm → ClRingoidWithInvolutionTerm)) 
     | primCl : (ClRingoidWithInvolutionTerm → ClRingoidWithInvolutionTerm)  
      open ClRingoidWithInvolutionTerm 
  
  inductive OpRingoidWithInvolutionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoidWithInvolutionTerm) 
     | timesOL : (OpRingoidWithInvolutionTerm → (OpRingoidWithInvolutionTerm → OpRingoidWithInvolutionTerm)) 
     | plusOL : (OpRingoidWithInvolutionTerm → (OpRingoidWithInvolutionTerm → OpRingoidWithInvolutionTerm)) 
     | primOL : (OpRingoidWithInvolutionTerm → OpRingoidWithInvolutionTerm)  
      open OpRingoidWithInvolutionTerm 
  
  inductive OpRingoidWithInvolutionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoidWithInvolutionTerm2) 
     | sing2 : (A → OpRingoidWithInvolutionTerm2) 
     | timesOL2 : (OpRingoidWithInvolutionTerm2 → (OpRingoidWithInvolutionTerm2 → OpRingoidWithInvolutionTerm2)) 
     | plusOL2 : (OpRingoidWithInvolutionTerm2 → (OpRingoidWithInvolutionTerm2 → OpRingoidWithInvolutionTerm2)) 
     | primOL2 : (OpRingoidWithInvolutionTerm2 → OpRingoidWithInvolutionTerm2)  
      open OpRingoidWithInvolutionTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRingoidWithInvolutionTerm A) → (ClRingoidWithInvolutionTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRingoidWithInvolutionTerm n) → (OpRingoidWithInvolutionTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRingoidWithInvolutionTerm2 n A) → (OpRingoidWithInvolutionTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RingoidWithInvolution A) → (RingoidWithInvolutionTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (primL x1) := ((prim Ri) (evalB Ri x1))  
  def evalCl   {A : Type}  : ((RingoidWithInvolution A) → ((ClRingoidWithInvolutionTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (primCl x1) := ((prim Ri) (evalCl Ri x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((RingoidWithInvolution A) → ((vector A n) → ((OpRingoidWithInvolutionTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (primOL x1) := ((prim Ri) (evalOpB Ri vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((RingoidWithInvolution A) → ((vector A n) → ((OpRingoidWithInvolutionTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (primOL2 x1) := ((prim Ri) (evalOp Ri vars x1))  
  def inductionB   (P : (RingoidWithInvolutionTerm → Type))  : ((∀ (x1 x2 : RingoidWithInvolutionTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : RingoidWithInvolutionTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : RingoidWithInvolutionTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : RingoidWithInvolutionTerm) , (P x))))) 
  | ptimesl pplusl ppriml (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (primL x1) := (ppriml _ (inductionB ptimesl pplusl ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClRingoidWithInvolutionTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingoidWithInvolutionTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClRingoidWithInvolutionTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClRingoidWithInvolutionTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClRingoidWithInvolutionTerm A)) , (P x)))))) 
  | psing ptimescl ppluscl pprimcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl pprimcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl ppluscl pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpRingoidWithInvolutionTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingoidWithInvolutionTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpRingoidWithInvolutionTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpRingoidWithInvolutionTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpRingoidWithInvolutionTerm n)) , (P x)))))) 
  | pv ptimesol pplusol pprimol (v x1) := (pv x1)  
  | pv ptimesol pplusol pprimol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pplusol pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRingoidWithInvolutionTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingoidWithInvolutionTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRingoidWithInvolutionTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpRingoidWithInvolutionTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpRingoidWithInvolutionTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1))  
  def stageB  : (RingoidWithInvolutionTerm → (Staged RingoidWithInvolutionTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClRingoidWithInvolutionTerm A) → (Staged (ClRingoidWithInvolutionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpRingoidWithInvolutionTerm n) → (Staged (OpRingoidWithInvolutionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRingoidWithInvolutionTerm2 n A) → (Staged (OpRingoidWithInvolutionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end RingoidWithInvolution