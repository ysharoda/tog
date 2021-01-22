import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightRingoid   
  structure RightRingoid  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open RightRingoid
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightRingoid A1)) (Ri2 : (RightRingoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightRingoid A1)) (Ri2 : (RightRingoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2)))))) 
  
  inductive RightRingoidTerm   : Type  
     | timesL : (RightRingoidTerm → (RightRingoidTerm → RightRingoidTerm)) 
     | plusL : (RightRingoidTerm → (RightRingoidTerm → RightRingoidTerm))  
      open RightRingoidTerm 
  
  inductive ClRightRingoidTerm  (A : Type) : Type  
     | sing : (A → ClRightRingoidTerm) 
     | timesCl : (ClRightRingoidTerm → (ClRightRingoidTerm → ClRightRingoidTerm)) 
     | plusCl : (ClRightRingoidTerm → (ClRightRingoidTerm → ClRightRingoidTerm))  
      open ClRightRingoidTerm 
  
  inductive OpRightRingoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightRingoidTerm) 
     | timesOL : (OpRightRingoidTerm → (OpRightRingoidTerm → OpRightRingoidTerm)) 
     | plusOL : (OpRightRingoidTerm → (OpRightRingoidTerm → OpRightRingoidTerm))  
      open OpRightRingoidTerm 
  
  inductive OpRightRingoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightRingoidTerm2) 
     | sing2 : (A → OpRightRingoidTerm2) 
     | timesOL2 : (OpRightRingoidTerm2 → (OpRightRingoidTerm2 → OpRightRingoidTerm2)) 
     | plusOL2 : (OpRightRingoidTerm2 → (OpRightRingoidTerm2 → OpRightRingoidTerm2))  
      open OpRightRingoidTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightRingoidTerm A) → (ClRightRingoidTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightRingoidTerm n) → (OpRightRingoidTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightRingoidTerm2 n A) → (OpRightRingoidTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightRingoid A) → (RightRingoidTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightRingoid A) → ((ClRightRingoidTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightRingoid A) → ((vector A n) → ((OpRightRingoidTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightRingoid A) → ((vector A n) → ((OpRightRingoidTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightRingoidTerm → Type)}  : ((∀ (x1 x2 : RightRingoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : RightRingoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : RightRingoidTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClRightRingoidTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightRingoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClRightRingoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClRightRingoidTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightRingoidTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightRingoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpRightRingoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpRightRingoidTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightRingoidTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRightRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpRightRingoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (RightRingoidTerm → (Staged RightRingoidTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightRingoidTerm A) → (Staged (ClRightRingoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightRingoidTerm n) → (Staged (OpRightRingoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightRingoidTerm2 n A) → (Staged (OpRightRingoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightRingoid