import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AssociativeRightRingoid   
  structure AssociativeRightRingoid  (A : Type) : Type := 
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (plus : (A → (A → A)))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open AssociativeRightRingoid
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (As1 : (AssociativeRightRingoid A1)) (As2 : (AssociativeRightRingoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times As1) x1 x2)) = ((times As2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus As1) x1 x2)) = ((plus As2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (As1 : (AssociativeRightRingoid A1)) (As2 : (AssociativeRightRingoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times As1) x1 x2) ((times As2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus As1) x1 x2) ((plus As2) y1 y2)))))) 
  
  inductive AssociativeRightRingoidTerm   : Type  
     | timesL : (AssociativeRightRingoidTerm → (AssociativeRightRingoidTerm → AssociativeRightRingoidTerm)) 
     | plusL : (AssociativeRightRingoidTerm → (AssociativeRightRingoidTerm → AssociativeRightRingoidTerm))  
      open AssociativeRightRingoidTerm 
  
  inductive ClAssociativeRightRingoidTerm  (A : Type) : Type  
     | sing : (A → ClAssociativeRightRingoidTerm) 
     | timesCl : (ClAssociativeRightRingoidTerm → (ClAssociativeRightRingoidTerm → ClAssociativeRightRingoidTerm)) 
     | plusCl : (ClAssociativeRightRingoidTerm → (ClAssociativeRightRingoidTerm → ClAssociativeRightRingoidTerm))  
      open ClAssociativeRightRingoidTerm 
  
  inductive OpAssociativeRightRingoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAssociativeRightRingoidTerm) 
     | timesOL : (OpAssociativeRightRingoidTerm → (OpAssociativeRightRingoidTerm → OpAssociativeRightRingoidTerm)) 
     | plusOL : (OpAssociativeRightRingoidTerm → (OpAssociativeRightRingoidTerm → OpAssociativeRightRingoidTerm))  
      open OpAssociativeRightRingoidTerm 
  
  inductive OpAssociativeRightRingoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAssociativeRightRingoidTerm2) 
     | sing2 : (A → OpAssociativeRightRingoidTerm2) 
     | timesOL2 : (OpAssociativeRightRingoidTerm2 → (OpAssociativeRightRingoidTerm2 → OpAssociativeRightRingoidTerm2)) 
     | plusOL2 : (OpAssociativeRightRingoidTerm2 → (OpAssociativeRightRingoidTerm2 → OpAssociativeRightRingoidTerm2))  
      open OpAssociativeRightRingoidTerm2 
  
  def simplifyCl   {A : Type}  : ((ClAssociativeRightRingoidTerm A) → (ClAssociativeRightRingoidTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpAssociativeRightRingoidTerm n) → (OpAssociativeRightRingoidTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpAssociativeRightRingoidTerm2 n A) → (OpAssociativeRightRingoidTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AssociativeRightRingoid A) → (AssociativeRightRingoidTerm → A)) 
  | As (timesL x1 x2) := ((times As) (evalB As x1) (evalB As x2))  
  | As (plusL x1 x2) := ((plus As) (evalB As x1) (evalB As x2))  
  def evalCl   {A : Type}  : ((AssociativeRightRingoid A) → ((ClAssociativeRightRingoidTerm A) → A)) 
  | As (sing x1) := x1  
  | As (timesCl x1 x2) := ((times As) (evalCl As x1) (evalCl As x2))  
  | As (plusCl x1 x2) := ((plus As) (evalCl As x1) (evalCl As x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((AssociativeRightRingoid A) → ((vector A n) → ((OpAssociativeRightRingoidTerm n) → A))) 
  | As vars (v x1) := (nth vars x1)  
  | As vars (timesOL x1 x2) := ((times As) (evalOpB As vars x1) (evalOpB As vars x2))  
  | As vars (plusOL x1 x2) := ((plus As) (evalOpB As vars x1) (evalOpB As vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((AssociativeRightRingoid A) → ((vector A n) → ((OpAssociativeRightRingoidTerm2 n A) → A))) 
  | As vars (v2 x1) := (nth vars x1)  
  | As vars (sing2 x1) := x1  
  | As vars (timesOL2 x1 x2) := ((times As) (evalOp As vars x1) (evalOp As vars x2))  
  | As vars (plusOL2 x1 x2) := ((plus As) (evalOp As vars x1) (evalOp As vars x2))  
  def inductionB   {P : (AssociativeRightRingoidTerm → Type)}  : ((∀ (x1 x2 : AssociativeRightRingoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : AssociativeRightRingoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : AssociativeRightRingoidTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClAssociativeRightRingoidTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAssociativeRightRingoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClAssociativeRightRingoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClAssociativeRightRingoidTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpAssociativeRightRingoidTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAssociativeRightRingoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpAssociativeRightRingoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpAssociativeRightRingoidTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpAssociativeRightRingoidTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAssociativeRightRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpAssociativeRightRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpAssociativeRightRingoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (AssociativeRightRingoidTerm → (Staged AssociativeRightRingoidTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClAssociativeRightRingoidTerm A) → (Staged (ClAssociativeRightRingoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpAssociativeRightRingoidTerm n) → (Staged (OpAssociativeRightRingoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpAssociativeRightRingoidTerm2 n A) → (Staged (OpAssociativeRightRingoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AssociativeRightRingoid