import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section NearSemiring   
  structure NearSemiring  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open NearSemiring
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ne1 : (NearSemiring A1)) (Ne2 : (NearSemiring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ne1) x1 x2)) = ((times Ne2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ne1) x1 x2)) = ((plus Ne2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ne1 : (NearSemiring A1)) (Ne2 : (NearSemiring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ne1) x1 x2) ((times Ne2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ne1) x1 x2) ((plus Ne2) y1 y2)))))) 
  
  inductive NearSemiringTerm   : Type  
     | timesL : (NearSemiringTerm → (NearSemiringTerm → NearSemiringTerm)) 
     | plusL : (NearSemiringTerm → (NearSemiringTerm → NearSemiringTerm))  
      open NearSemiringTerm 
  
  inductive ClNearSemiringTerm  (A : Type) : Type  
     | sing : (A → ClNearSemiringTerm) 
     | timesCl : (ClNearSemiringTerm → (ClNearSemiringTerm → ClNearSemiringTerm)) 
     | plusCl : (ClNearSemiringTerm → (ClNearSemiringTerm → ClNearSemiringTerm))  
      open ClNearSemiringTerm 
  
  inductive OpNearSemiringTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpNearSemiringTerm) 
     | timesOL : (OpNearSemiringTerm → (OpNearSemiringTerm → OpNearSemiringTerm)) 
     | plusOL : (OpNearSemiringTerm → (OpNearSemiringTerm → OpNearSemiringTerm))  
      open OpNearSemiringTerm 
  
  inductive OpNearSemiringTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpNearSemiringTerm2) 
     | sing2 : (A → OpNearSemiringTerm2) 
     | timesOL2 : (OpNearSemiringTerm2 → (OpNearSemiringTerm2 → OpNearSemiringTerm2)) 
     | plusOL2 : (OpNearSemiringTerm2 → (OpNearSemiringTerm2 → OpNearSemiringTerm2))  
      open OpNearSemiringTerm2 
  
  def simplifyCl   (A : Type)  : ((ClNearSemiringTerm A) → (ClNearSemiringTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpNearSemiringTerm n) → (OpNearSemiringTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpNearSemiringTerm2 n A) → (OpNearSemiringTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((NearSemiring A) → (NearSemiringTerm → A)) 
  | Ne (timesL x1 x2) := ((times Ne) (evalB Ne x1) (evalB Ne x2))  
  | Ne (plusL x1 x2) := ((plus Ne) (evalB Ne x1) (evalB Ne x2))  
  def evalCl   {A : Type}  : ((NearSemiring A) → ((ClNearSemiringTerm A) → A)) 
  | Ne (sing x1) := x1  
  | Ne (timesCl x1 x2) := ((times Ne) (evalCl Ne x1) (evalCl Ne x2))  
  | Ne (plusCl x1 x2) := ((plus Ne) (evalCl Ne x1) (evalCl Ne x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((NearSemiring A) → ((vector A n) → ((OpNearSemiringTerm n) → A))) 
  | Ne vars (v x1) := (nth vars x1)  
  | Ne vars (timesOL x1 x2) := ((times Ne) (evalOpB Ne vars x1) (evalOpB Ne vars x2))  
  | Ne vars (plusOL x1 x2) := ((plus Ne) (evalOpB Ne vars x1) (evalOpB Ne vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((NearSemiring A) → ((vector A n) → ((OpNearSemiringTerm2 n A) → A))) 
  | Ne vars (v2 x1) := (nth vars x1)  
  | Ne vars (sing2 x1) := x1  
  | Ne vars (timesOL2 x1 x2) := ((times Ne) (evalOp Ne vars x1) (evalOp Ne vars x2))  
  | Ne vars (plusOL2 x1 x2) := ((plus Ne) (evalOp Ne vars x1) (evalOp Ne vars x2))  
  def inductionB   (P : (NearSemiringTerm → Type))  : ((∀ (x1 x2 : NearSemiringTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : NearSemiringTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : NearSemiringTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClNearSemiringTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClNearSemiringTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClNearSemiringTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClNearSemiringTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpNearSemiringTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpNearSemiringTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpNearSemiringTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpNearSemiringTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpNearSemiringTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpNearSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpNearSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpNearSemiringTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (NearSemiringTerm → (Staged NearSemiringTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClNearSemiringTerm A) → (Staged (ClNearSemiringTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpNearSemiringTerm n) → (Staged (OpNearSemiringTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpNearSemiringTerm2 n A) → (Staged (OpNearSemiringTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end NearSemiring