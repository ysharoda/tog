import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftRingoid   
  structure LeftRingoid  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z)))) 
  
  open LeftRingoid
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftRingoid A1)) (Le2 : (LeftRingoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Le1) x1 x2)) = ((times Le2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Le1) x1 x2)) = ((plus Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftRingoid A1)) (Le2 : (LeftRingoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Le1) x1 x2) ((times Le2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Le1) x1 x2) ((plus Le2) y1 y2)))))) 
  
  inductive LeftRingoidTerm   : Type  
     | timesL : (LeftRingoidTerm → (LeftRingoidTerm → LeftRingoidTerm)) 
     | plusL : (LeftRingoidTerm → (LeftRingoidTerm → LeftRingoidTerm))  
      open LeftRingoidTerm 
  
  inductive ClLeftRingoidTerm  (A : Type) : Type  
     | sing : (A → ClLeftRingoidTerm) 
     | timesCl : (ClLeftRingoidTerm → (ClLeftRingoidTerm → ClLeftRingoidTerm)) 
     | plusCl : (ClLeftRingoidTerm → (ClLeftRingoidTerm → ClLeftRingoidTerm))  
      open ClLeftRingoidTerm 
  
  inductive OpLeftRingoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftRingoidTerm) 
     | timesOL : (OpLeftRingoidTerm → (OpLeftRingoidTerm → OpLeftRingoidTerm)) 
     | plusOL : (OpLeftRingoidTerm → (OpLeftRingoidTerm → OpLeftRingoidTerm))  
      open OpLeftRingoidTerm 
  
  inductive OpLeftRingoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftRingoidTerm2) 
     | sing2 : (A → OpLeftRingoidTerm2) 
     | timesOL2 : (OpLeftRingoidTerm2 → (OpLeftRingoidTerm2 → OpLeftRingoidTerm2)) 
     | plusOL2 : (OpLeftRingoidTerm2 → (OpLeftRingoidTerm2 → OpLeftRingoidTerm2))  
      open OpLeftRingoidTerm2 
  
  def simplifyCl   (A : Type)  : ((ClLeftRingoidTerm A) → (ClLeftRingoidTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpLeftRingoidTerm n) → (OpLeftRingoidTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpLeftRingoidTerm2 n A) → (OpLeftRingoidTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftRingoid A) → (LeftRingoidTerm → A)) 
  | Le (timesL x1 x2) := ((times Le) (evalB Le x1) (evalB Le x2))  
  | Le (plusL x1 x2) := ((plus Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftRingoid A) → ((ClLeftRingoidTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (timesCl x1 x2) := ((times Le) (evalCl Le x1) (evalCl Le x2))  
  | Le (plusCl x1 x2) := ((plus Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((LeftRingoid A) → ((vector A n) → ((OpLeftRingoidTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (timesOL x1 x2) := ((times Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  | Le vars (plusOL x1 x2) := ((plus Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((LeftRingoid A) → ((vector A n) → ((OpLeftRingoidTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (timesOL2 x1 x2) := ((times Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  | Le vars (plusOL2 x1 x2) := ((plus Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   (P : (LeftRingoidTerm → Type))  : ((∀ (x1 x2 : LeftRingoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : LeftRingoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : LeftRingoidTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClLeftRingoidTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftRingoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClLeftRingoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClLeftRingoidTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpLeftRingoidTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftRingoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpLeftRingoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpLeftRingoidTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpLeftRingoidTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpLeftRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpLeftRingoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (LeftRingoidTerm → (Staged LeftRingoidTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClLeftRingoidTerm A) → (Staged (ClLeftRingoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpLeftRingoidTerm n) → (Staged (OpLeftRingoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpLeftRingoidTerm2 n A) → (Staged (OpLeftRingoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftRingoid