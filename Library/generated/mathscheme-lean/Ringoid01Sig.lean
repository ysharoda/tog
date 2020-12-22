import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Ringoid01Sig   
  structure Ringoid01Sig  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (zero : A)
       (one : A) 
  
  open Ringoid01Sig
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (oneP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid01Sig A1)) (Ri2 : (Ringoid01Sig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ri1)) = (zero Ri2))
       (pres_one : (hom (one Ri1)) = (one Ri2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid01Sig A1)) (Ri2 : (Ringoid01Sig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2))))))
       (interp_zero : (interp (zero Ri1) (zero Ri2)))
       (interp_one : (interp (one Ri1) (one Ri2))) 
  
  inductive Ringoid01SigTerm   : Type  
     | timesL : (Ringoid01SigTerm → (Ringoid01SigTerm → Ringoid01SigTerm)) 
     | plusL : (Ringoid01SigTerm → (Ringoid01SigTerm → Ringoid01SigTerm)) 
     | zeroL : Ringoid01SigTerm 
     | oneL : Ringoid01SigTerm  
      open Ringoid01SigTerm 
  
  inductive ClRingoid01SigTerm  (A : Type) : Type  
     | sing : (A → ClRingoid01SigTerm) 
     | timesCl : (ClRingoid01SigTerm → (ClRingoid01SigTerm → ClRingoid01SigTerm)) 
     | plusCl : (ClRingoid01SigTerm → (ClRingoid01SigTerm → ClRingoid01SigTerm)) 
     | zeroCl : ClRingoid01SigTerm 
     | oneCl : ClRingoid01SigTerm  
      open ClRingoid01SigTerm 
  
  inductive OpRingoid01SigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoid01SigTerm) 
     | timesOL : (OpRingoid01SigTerm → (OpRingoid01SigTerm → OpRingoid01SigTerm)) 
     | plusOL : (OpRingoid01SigTerm → (OpRingoid01SigTerm → OpRingoid01SigTerm)) 
     | zeroOL : OpRingoid01SigTerm 
     | oneOL : OpRingoid01SigTerm  
      open OpRingoid01SigTerm 
  
  inductive OpRingoid01SigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoid01SigTerm2) 
     | sing2 : (A → OpRingoid01SigTerm2) 
     | timesOL2 : (OpRingoid01SigTerm2 → (OpRingoid01SigTerm2 → OpRingoid01SigTerm2)) 
     | plusOL2 : (OpRingoid01SigTerm2 → (OpRingoid01SigTerm2 → OpRingoid01SigTerm2)) 
     | zeroOL2 : OpRingoid01SigTerm2 
     | oneOL2 : OpRingoid01SigTerm2  
      open OpRingoid01SigTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRingoid01SigTerm A) → (ClRingoid01SigTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRingoid01SigTerm n) → (OpRingoid01SigTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRingoid01SigTerm2 n A) → (OpRingoid01SigTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Ringoid01Sig A) → (Ringoid01SigTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri zeroL := (zero Ri)  
  | Ri oneL := (one Ri)  
  def evalCl   {A : Type}  : ((Ringoid01Sig A) → ((ClRingoid01SigTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri zeroCl := (zero Ri)  
  | Ri oneCl := (one Ri)  
  def evalOpB   {A : Type} (n : ℕ)  : ((Ringoid01Sig A) → ((vector A n) → ((OpRingoid01SigTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars zeroOL := (zero Ri)  
  | Ri vars oneOL := (one Ri)  
  def evalOp   {A : Type} (n : ℕ)  : ((Ringoid01Sig A) → ((vector A n) → ((OpRingoid01SigTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars zeroOL2 := (zero Ri)  
  | Ri vars oneOL2 := (one Ri)  
  def inductionB   (P : (Ringoid01SigTerm → Type))  : ((∀ (x1 x2 : Ringoid01SigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : Ringoid01SigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((P oneL) → (∀ (x : Ringoid01SigTerm) , (P x)))))) 
  | ptimesl pplusl p0l p1l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p0l p1l x1) (inductionB ptimesl pplusl p0l p1l x2))  
  | ptimesl pplusl p0l p1l (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p0l p1l x1) (inductionB ptimesl pplusl p0l p1l x2))  
  | ptimesl pplusl p0l p1l zeroL := p0l  
  | ptimesl pplusl p0l p1l oneL := p1l  
  def inductionCl   (A : Type) (P : ((ClRingoid01SigTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingoid01SigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClRingoid01SigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((P oneCl) → (∀ (x : (ClRingoid01SigTerm A)) , (P x))))))) 
  | psing ptimescl ppluscl p0cl p1cl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p0cl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p0cl p1cl x1) (inductionCl psing ptimescl ppluscl p0cl p1cl x2))  
  | psing ptimescl ppluscl p0cl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p0cl p1cl x1) (inductionCl psing ptimescl ppluscl p0cl p1cl x2))  
  | psing ptimescl ppluscl p0cl p1cl zeroCl := p0cl  
  | psing ptimescl ppluscl p0cl p1cl oneCl := p1cl  
  def inductionOpB   (n : ℕ) (P : ((OpRingoid01SigTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingoid01SigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpRingoid01SigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((P oneOL) → (∀ (x : (OpRingoid01SigTerm n)) , (P x))))))) 
  | pv ptimesol pplusol p0ol p1ol (v x1) := (pv x1)  
  | pv ptimesol pplusol p0ol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p0ol p1ol x1) (inductionOpB pv ptimesol pplusol p0ol p1ol x2))  
  | pv ptimesol pplusol p0ol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p0ol p1ol x1) (inductionOpB pv ptimesol pplusol p0ol p1ol x2))  
  | pv ptimesol pplusol p0ol p1ol zeroOL := p0ol  
  | pv ptimesol pplusol p0ol p1ol oneOL := p1ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRingoid01SigTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingoid01SigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRingoid01SigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((P oneOL2) → (∀ (x : (OpRingoid01SigTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (Ringoid01SigTerm → (Staged Ringoid01SigTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | oneL := (Now oneL)  
  def stageCl   (A : Type)  : ((ClRingoid01SigTerm A) → (Staged (ClRingoid01SigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | oneCl := (Now oneCl)  
  def stageOpB   (n : ℕ)  : ((OpRingoid01SigTerm n) → (Staged (OpRingoid01SigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | oneOL := (Now oneOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRingoid01SigTerm2 n A) → (Staged (OpRingoid01SigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (oneT : (Repr A)) 
  
end Ringoid01Sig