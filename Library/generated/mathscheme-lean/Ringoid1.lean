import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Ringoid1   
  structure Ringoid1  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (one : A)
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open Ringoid1
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid1 A1)) (Ri2 : (Ringoid1 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2))))
       (pres_one : (hom (one Ri1)) = (one Ri2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid1 A1)) (Ri2 : (Ringoid1 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2))))))
       (interp_one : (interp (one Ri1) (one Ri2))) 
  
  inductive Ringoid1LTerm   : Type  
     | timesL : (Ringoid1LTerm → (Ringoid1LTerm → Ringoid1LTerm)) 
     | plusL : (Ringoid1LTerm → (Ringoid1LTerm → Ringoid1LTerm)) 
     | oneL : Ringoid1LTerm  
      open Ringoid1LTerm 
  
  inductive ClRingoid1ClTerm  (A : Type) : Type  
     | sing : (A → ClRingoid1ClTerm) 
     | timesCl : (ClRingoid1ClTerm → (ClRingoid1ClTerm → ClRingoid1ClTerm)) 
     | plusCl : (ClRingoid1ClTerm → (ClRingoid1ClTerm → ClRingoid1ClTerm)) 
     | oneCl : ClRingoid1ClTerm  
      open ClRingoid1ClTerm 
  
  inductive OpRingoid1OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoid1OLTerm) 
     | timesOL : (OpRingoid1OLTerm → (OpRingoid1OLTerm → OpRingoid1OLTerm)) 
     | plusOL : (OpRingoid1OLTerm → (OpRingoid1OLTerm → OpRingoid1OLTerm)) 
     | oneOL : OpRingoid1OLTerm  
      open OpRingoid1OLTerm 
  
  inductive OpRingoid1OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoid1OL2Term2) 
     | sing2 : (A → OpRingoid1OL2Term2) 
     | timesOL2 : (OpRingoid1OL2Term2 → (OpRingoid1OL2Term2 → OpRingoid1OL2Term2)) 
     | plusOL2 : (OpRingoid1OL2Term2 → (OpRingoid1OL2Term2 → OpRingoid1OL2Term2)) 
     | oneOL2 : OpRingoid1OL2Term2  
      open OpRingoid1OL2Term2 
  
  def simplifyCl   (A : Type)  : ((ClRingoid1ClTerm A) → (ClRingoid1ClTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRingoid1OLTerm n) → (OpRingoid1OLTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRingoid1OL2Term2 n A) → (OpRingoid1OL2Term2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Ringoid1 A) → (Ringoid1LTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri oneL := (one Ri)  
  def evalCl   {A : Type}  : ((Ringoid1 A) → ((ClRingoid1ClTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri oneCl := (one Ri)  
  def evalOpB   {A : Type} (n : ℕ)  : ((Ringoid1 A) → ((vector A n) → ((OpRingoid1OLTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars oneOL := (one Ri)  
  def evalOp   {A : Type} (n : ℕ)  : ((Ringoid1 A) → ((vector A n) → ((OpRingoid1OL2Term2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars oneOL2 := (one Ri)  
  def inductionB   (P : (Ringoid1LTerm → Type))  : ((∀ (x1 x2 : Ringoid1LTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : Ringoid1LTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P oneL) → (∀ (x : Ringoid1LTerm) , (P x))))) 
  | ptimesl pplusl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p1l x1) (inductionB ptimesl pplusl p1l x2))  
  | ptimesl pplusl p1l (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p1l x1) (inductionB ptimesl pplusl p1l x2))  
  | ptimesl pplusl p1l oneL := p1l  
  def inductionCl   (A : Type) (P : ((ClRingoid1ClTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingoid1ClTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClRingoid1ClTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P oneCl) → (∀ (x : (ClRingoid1ClTerm A)) , (P x)))))) 
  | psing ptimescl ppluscl p1cl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p1cl x1) (inductionCl psing ptimescl ppluscl p1cl x2))  
  | psing ptimescl ppluscl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p1cl x1) (inductionCl psing ptimescl ppluscl p1cl x2))  
  | psing ptimescl ppluscl p1cl oneCl := p1cl  
  def inductionOpB   (n : ℕ) (P : ((OpRingoid1OLTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingoid1OLTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpRingoid1OLTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P oneOL) → (∀ (x : (OpRingoid1OLTerm n)) , (P x)))))) 
  | pv ptimesol pplusol p1ol (v x1) := (pv x1)  
  | pv ptimesol pplusol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p1ol x1) (inductionOpB pv ptimesol pplusol p1ol x2))  
  | pv ptimesol pplusol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p1ol x1) (inductionOpB pv ptimesol pplusol p1ol x2))  
  | pv ptimesol pplusol p1ol oneOL := p1ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRingoid1OL2Term2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingoid1OL2Term2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRingoid1OL2Term2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P oneOL2) → (∀ (x : (OpRingoid1OL2Term2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (Ringoid1LTerm → (Staged Ringoid1LTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  def stageCl   (A : Type)  : ((ClRingoid1ClTerm A) → (Staged (ClRingoid1ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  def stageOpB   (n : ℕ)  : ((OpRingoid1OLTerm n) → (Staged (OpRingoid1OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRingoid1OL2Term2 n A) → (Staged (OpRingoid1OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A)) 
  
end Ringoid1