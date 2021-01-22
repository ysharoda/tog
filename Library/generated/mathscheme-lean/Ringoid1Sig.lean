import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Ringoid1Sig   
  structure Ringoid1Sig  (A : Type) : Type := 
       (times : (A → (A → A)))
       (one : A)
       (plus : (A → (A → A))) 
  
  open Ringoid1Sig
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS)
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid1Sig A1)) (Ri2 : (Ringoid1Sig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_one : (hom (one Ri1)) = (one Ri2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid1Sig A1)) (Ri2 : (Ringoid1Sig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_one : (interp (one Ri1) (one Ri2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2)))))) 
  
  inductive Ringoid1SigTerm   : Type  
     | timesL : (Ringoid1SigTerm → (Ringoid1SigTerm → Ringoid1SigTerm)) 
     | oneL : Ringoid1SigTerm 
     | plusL : (Ringoid1SigTerm → (Ringoid1SigTerm → Ringoid1SigTerm))  
      open Ringoid1SigTerm 
  
  inductive ClRingoid1SigTerm  (A : Type) : Type  
     | sing : (A → ClRingoid1SigTerm) 
     | timesCl : (ClRingoid1SigTerm → (ClRingoid1SigTerm → ClRingoid1SigTerm)) 
     | oneCl : ClRingoid1SigTerm 
     | plusCl : (ClRingoid1SigTerm → (ClRingoid1SigTerm → ClRingoid1SigTerm))  
      open ClRingoid1SigTerm 
  
  inductive OpRingoid1SigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoid1SigTerm) 
     | timesOL : (OpRingoid1SigTerm → (OpRingoid1SigTerm → OpRingoid1SigTerm)) 
     | oneOL : OpRingoid1SigTerm 
     | plusOL : (OpRingoid1SigTerm → (OpRingoid1SigTerm → OpRingoid1SigTerm))  
      open OpRingoid1SigTerm 
  
  inductive OpRingoid1SigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoid1SigTerm2) 
     | sing2 : (A → OpRingoid1SigTerm2) 
     | timesOL2 : (OpRingoid1SigTerm2 → (OpRingoid1SigTerm2 → OpRingoid1SigTerm2)) 
     | oneOL2 : OpRingoid1SigTerm2 
     | plusOL2 : (OpRingoid1SigTerm2 → (OpRingoid1SigTerm2 → OpRingoid1SigTerm2))  
      open OpRingoid1SigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRingoid1SigTerm A) → (ClRingoid1SigTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRingoid1SigTerm n) → (OpRingoid1SigTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRingoid1SigTerm2 n A) → (OpRingoid1SigTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Ringoid1Sig A) → (Ringoid1SigTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri oneL := (one Ri)  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((Ringoid1Sig A) → ((ClRingoid1SigTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri oneCl := (one Ri)  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Ringoid1Sig A) → ((vector A n) → ((OpRingoid1SigTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars oneOL := (one Ri)  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Ringoid1Sig A) → ((vector A n) → ((OpRingoid1SigTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars oneOL2 := (one Ri)  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (Ringoid1SigTerm → Type)}  : ((∀ (x1 x2 : Ringoid1SigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → ((∀ (x1 x2 : Ringoid1SigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : Ringoid1SigTerm) , (P x))))) 
  | ptimesl p1l pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l pplusl x1) (inductionB ptimesl p1l pplusl x2))  
  | ptimesl p1l pplusl oneL := p1l  
  | ptimesl p1l pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl p1l pplusl x1) (inductionB ptimesl p1l pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClRingoid1SigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingoid1SigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → ((∀ (x1 x2 : (ClRingoid1SigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClRingoid1SigTerm A)) , (P x)))))) 
  | psing ptimescl p1cl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl p1cl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl ppluscl x1) (inductionCl psing ptimescl p1cl ppluscl x2))  
  | psing ptimescl p1cl ppluscl oneCl := p1cl  
  | psing ptimescl p1cl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl p1cl ppluscl x1) (inductionCl psing ptimescl p1cl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRingoid1SigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingoid1SigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → ((∀ (x1 x2 : (OpRingoid1SigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpRingoid1SigTerm n)) , (P x)))))) 
  | pv ptimesol p1ol pplusol (v x1) := (pv x1)  
  | pv ptimesol p1ol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol pplusol x1) (inductionOpB pv ptimesol p1ol pplusol x2))  
  | pv ptimesol p1ol pplusol oneOL := p1ol  
  | pv ptimesol p1ol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol p1ol pplusol x1) (inductionOpB pv ptimesol p1ol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRingoid1SigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingoid1SigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 x2 : (OpRingoid1SigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpRingoid1SigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x2))  
  def stageB  : (Ringoid1SigTerm → (Staged Ringoid1SigTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRingoid1SigTerm A) → (Staged (ClRingoid1SigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRingoid1SigTerm n) → (Staged (OpRingoid1SigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRingoid1SigTerm2 n A) → (Staged (OpRingoid1SigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Ringoid1Sig