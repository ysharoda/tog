import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Ringoid0Sig   
  structure Ringoid0Sig  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (times : (A → (A → A))) 
  
  open Ringoid0Sig
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid0Sig A1)) (Ri2 : (Ringoid0Sig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ri1)) = (zero Ri2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (Ringoid0Sig A1)) (Ri2 : (Ringoid0Sig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ri1) (zero Ri2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2)))))) 
  
  inductive Ringoid0SigTerm   : Type  
     | zeroL : Ringoid0SigTerm 
     | plusL : (Ringoid0SigTerm → (Ringoid0SigTerm → Ringoid0SigTerm)) 
     | timesL : (Ringoid0SigTerm → (Ringoid0SigTerm → Ringoid0SigTerm))  
      open Ringoid0SigTerm 
  
  inductive ClRingoid0SigTerm  (A : Type) : Type  
     | sing : (A → ClRingoid0SigTerm) 
     | zeroCl : ClRingoid0SigTerm 
     | plusCl : (ClRingoid0SigTerm → (ClRingoid0SigTerm → ClRingoid0SigTerm)) 
     | timesCl : (ClRingoid0SigTerm → (ClRingoid0SigTerm → ClRingoid0SigTerm))  
      open ClRingoid0SigTerm 
  
  inductive OpRingoid0SigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingoid0SigTerm) 
     | zeroOL : OpRingoid0SigTerm 
     | plusOL : (OpRingoid0SigTerm → (OpRingoid0SigTerm → OpRingoid0SigTerm)) 
     | timesOL : (OpRingoid0SigTerm → (OpRingoid0SigTerm → OpRingoid0SigTerm))  
      open OpRingoid0SigTerm 
  
  inductive OpRingoid0SigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingoid0SigTerm2) 
     | sing2 : (A → OpRingoid0SigTerm2) 
     | zeroOL2 : OpRingoid0SigTerm2 
     | plusOL2 : (OpRingoid0SigTerm2 → (OpRingoid0SigTerm2 → OpRingoid0SigTerm2)) 
     | timesOL2 : (OpRingoid0SigTerm2 → (OpRingoid0SigTerm2 → OpRingoid0SigTerm2))  
      open OpRingoid0SigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRingoid0SigTerm A) → (ClRingoid0SigTerm A)) 
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRingoid0SigTerm n) → (OpRingoid0SigTerm n)) 
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRingoid0SigTerm2 n A) → (OpRingoid0SigTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Ringoid0Sig A) → (Ringoid0SigTerm → A)) 
  | Ri zeroL := (zero Ri)  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((Ringoid0Sig A) → ((ClRingoid0SigTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri zeroCl := (zero Ri)  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Ringoid0Sig A) → ((vector A n) → ((OpRingoid0SigTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars zeroOL := (zero Ri)  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Ringoid0Sig A) → ((vector A n) → ((OpRingoid0SigTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars zeroOL2 := (zero Ri)  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (Ringoid0SigTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : Ringoid0SigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : Ringoid0SigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : Ringoid0SigTerm) , (P x))))) 
  | p0l pplusl ptimesl zeroL := p0l  
  | p0l pplusl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl ptimesl x1) (inductionB p0l pplusl ptimesl x2))  
  | p0l pplusl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l pplusl ptimesl x1) (inductionB p0l pplusl ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClRingoid0SigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClRingoid0SigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClRingoid0SigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClRingoid0SigTerm A)) , (P x)))))) 
  | psing p0cl ppluscl ptimescl (sing x1) := (psing x1)  
  | psing p0cl ppluscl ptimescl zeroCl := p0cl  
  | psing p0cl ppluscl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl ptimescl x1) (inductionCl psing p0cl ppluscl ptimescl x2))  
  | psing p0cl ppluscl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ppluscl ptimescl x1) (inductionCl psing p0cl ppluscl ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRingoid0SigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpRingoid0SigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpRingoid0SigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpRingoid0SigTerm n)) , (P x)))))) 
  | pv p0ol pplusol ptimesol (v x1) := (pv x1)  
  | pv p0ol pplusol ptimesol zeroOL := p0ol  
  | pv p0ol pplusol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol ptimesol x1) (inductionOpB pv p0ol pplusol ptimesol x2))  
  | pv p0ol pplusol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol pplusol ptimesol x1) (inductionOpB pv p0ol pplusol ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRingoid0SigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpRingoid0SigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRingoid0SigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpRingoid0SigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x2))  
  def stageB  : (Ringoid0SigTerm → (Staged Ringoid0SigTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRingoid0SigTerm A) → (Staged (ClRingoid0SigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRingoid0SigTerm n) → (Staged (OpRingoid0SigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRingoid0SigTerm2 n A) → (Staged (OpRingoid0SigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Ringoid0Sig