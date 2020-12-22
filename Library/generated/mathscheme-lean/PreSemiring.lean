import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PreSemiring   
  structure PreSemiring  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open PreSemiring
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Pr1 : (PreSemiring A1)) (Pr2 : (PreSemiring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Pr1) x1 x2)) = ((times Pr2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Pr1) x1 x2)) = ((plus Pr2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Pr1 : (PreSemiring A1)) (Pr2 : (PreSemiring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Pr1) x1 x2) ((times Pr2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Pr1) x1 x2) ((plus Pr2) y1 y2)))))) 
  
  inductive PreSemiringTerm   : Type  
     | timesL : (PreSemiringTerm → (PreSemiringTerm → PreSemiringTerm)) 
     | plusL : (PreSemiringTerm → (PreSemiringTerm → PreSemiringTerm))  
      open PreSemiringTerm 
  
  inductive ClPreSemiringTerm  (A : Type) : Type  
     | sing : (A → ClPreSemiringTerm) 
     | timesCl : (ClPreSemiringTerm → (ClPreSemiringTerm → ClPreSemiringTerm)) 
     | plusCl : (ClPreSemiringTerm → (ClPreSemiringTerm → ClPreSemiringTerm))  
      open ClPreSemiringTerm 
  
  inductive OpPreSemiringTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPreSemiringTerm) 
     | timesOL : (OpPreSemiringTerm → (OpPreSemiringTerm → OpPreSemiringTerm)) 
     | plusOL : (OpPreSemiringTerm → (OpPreSemiringTerm → OpPreSemiringTerm))  
      open OpPreSemiringTerm 
  
  inductive OpPreSemiringTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPreSemiringTerm2) 
     | sing2 : (A → OpPreSemiringTerm2) 
     | timesOL2 : (OpPreSemiringTerm2 → (OpPreSemiringTerm2 → OpPreSemiringTerm2)) 
     | plusOL2 : (OpPreSemiringTerm2 → (OpPreSemiringTerm2 → OpPreSemiringTerm2))  
      open OpPreSemiringTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPreSemiringTerm A) → (ClPreSemiringTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPreSemiringTerm n) → (OpPreSemiringTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPreSemiringTerm2 n A) → (OpPreSemiringTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PreSemiring A) → (PreSemiringTerm → A)) 
  | Pr (timesL x1 x2) := ((times Pr) (evalB Pr x1) (evalB Pr x2))  
  | Pr (plusL x1 x2) := ((plus Pr) (evalB Pr x1) (evalB Pr x2))  
  def evalCl   {A : Type}  : ((PreSemiring A) → ((ClPreSemiringTerm A) → A)) 
  | Pr (sing x1) := x1  
  | Pr (timesCl x1 x2) := ((times Pr) (evalCl Pr x1) (evalCl Pr x2))  
  | Pr (plusCl x1 x2) := ((plus Pr) (evalCl Pr x1) (evalCl Pr x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((PreSemiring A) → ((vector A n) → ((OpPreSemiringTerm n) → A))) 
  | Pr vars (v x1) := (nth vars x1)  
  | Pr vars (timesOL x1 x2) := ((times Pr) (evalOpB Pr vars x1) (evalOpB Pr vars x2))  
  | Pr vars (plusOL x1 x2) := ((plus Pr) (evalOpB Pr vars x1) (evalOpB Pr vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((PreSemiring A) → ((vector A n) → ((OpPreSemiringTerm2 n A) → A))) 
  | Pr vars (v2 x1) := (nth vars x1)  
  | Pr vars (sing2 x1) := x1  
  | Pr vars (timesOL2 x1 x2) := ((times Pr) (evalOp Pr vars x1) (evalOp Pr vars x2))  
  | Pr vars (plusOL2 x1 x2) := ((plus Pr) (evalOp Pr vars x1) (evalOp Pr vars x2))  
  def inductionB   (P : (PreSemiringTerm → Type))  : ((∀ (x1 x2 : PreSemiringTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : PreSemiringTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : PreSemiringTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClPreSemiringTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPreSemiringTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClPreSemiringTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClPreSemiringTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpPreSemiringTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPreSemiringTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpPreSemiringTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpPreSemiringTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPreSemiringTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPreSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpPreSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpPreSemiringTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (PreSemiringTerm → (Staged PreSemiringTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClPreSemiringTerm A) → (Staged (ClPreSemiringTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpPreSemiringTerm n) → (Staged (OpPreSemiringTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPreSemiringTerm2 n A) → (Staged (OpPreSemiringTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end PreSemiring