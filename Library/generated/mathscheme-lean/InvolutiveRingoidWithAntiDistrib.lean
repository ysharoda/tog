import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveRingoidWithAntiDistrib   
  structure InvolutiveRingoidWithAntiDistrib  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (prim : (A → A))
       (antidis_prim_plus : (∀ {x y : A} , (prim (plus x y)) = (plus (prim y) (prim x))))
       (antidis_prim_times : (∀ {x y : A} , (prim (times x y)) = (times (prim y) (prim x)))) 
  
  open InvolutiveRingoidWithAntiDistrib
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
       (antidis_prim_plusP : (∀ {xP yP : (Prod A A)} , (primP (plusP xP yP)) = (plusP (primP yP) (primP xP))))
       (antidis_prim_timesP : (∀ {xP yP : (Prod A A)} , (primP (timesP xP yP)) = (timesP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRingoidWithAntiDistrib A1)) (In2 : (InvolutiveRingoidWithAntiDistrib A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times In1) x1 x2)) = ((times In2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus In1) x1 x2)) = ((plus In2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRingoidWithAntiDistrib A1)) (In2 : (InvolutiveRingoidWithAntiDistrib A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times In1) x1 x2) ((times In2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus In1) x1 x2) ((plus In2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutiveRingoidWithAntiDistribTerm   : Type  
     | timesL : (InvolutiveRingoidWithAntiDistribTerm → (InvolutiveRingoidWithAntiDistribTerm → InvolutiveRingoidWithAntiDistribTerm)) 
     | plusL : (InvolutiveRingoidWithAntiDistribTerm → (InvolutiveRingoidWithAntiDistribTerm → InvolutiveRingoidWithAntiDistribTerm)) 
     | primL : (InvolutiveRingoidWithAntiDistribTerm → InvolutiveRingoidWithAntiDistribTerm)  
      open InvolutiveRingoidWithAntiDistribTerm 
  
  inductive ClInvolutiveRingoidWithAntiDistribTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveRingoidWithAntiDistribTerm) 
     | timesCl : (ClInvolutiveRingoidWithAntiDistribTerm → (ClInvolutiveRingoidWithAntiDistribTerm → ClInvolutiveRingoidWithAntiDistribTerm)) 
     | plusCl : (ClInvolutiveRingoidWithAntiDistribTerm → (ClInvolutiveRingoidWithAntiDistribTerm → ClInvolutiveRingoidWithAntiDistribTerm)) 
     | primCl : (ClInvolutiveRingoidWithAntiDistribTerm → ClInvolutiveRingoidWithAntiDistribTerm)  
      open ClInvolutiveRingoidWithAntiDistribTerm 
  
  inductive OpInvolutiveRingoidWithAntiDistribTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveRingoidWithAntiDistribTerm) 
     | timesOL : (OpInvolutiveRingoidWithAntiDistribTerm → (OpInvolutiveRingoidWithAntiDistribTerm → OpInvolutiveRingoidWithAntiDistribTerm)) 
     | plusOL : (OpInvolutiveRingoidWithAntiDistribTerm → (OpInvolutiveRingoidWithAntiDistribTerm → OpInvolutiveRingoidWithAntiDistribTerm)) 
     | primOL : (OpInvolutiveRingoidWithAntiDistribTerm → OpInvolutiveRingoidWithAntiDistribTerm)  
      open OpInvolutiveRingoidWithAntiDistribTerm 
  
  inductive OpInvolutiveRingoidWithAntiDistribTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveRingoidWithAntiDistribTerm2) 
     | sing2 : (A → OpInvolutiveRingoidWithAntiDistribTerm2) 
     | timesOL2 : (OpInvolutiveRingoidWithAntiDistribTerm2 → (OpInvolutiveRingoidWithAntiDistribTerm2 → OpInvolutiveRingoidWithAntiDistribTerm2)) 
     | plusOL2 : (OpInvolutiveRingoidWithAntiDistribTerm2 → (OpInvolutiveRingoidWithAntiDistribTerm2 → OpInvolutiveRingoidWithAntiDistribTerm2)) 
     | primOL2 : (OpInvolutiveRingoidWithAntiDistribTerm2 → OpInvolutiveRingoidWithAntiDistribTerm2)  
      open OpInvolutiveRingoidWithAntiDistribTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutiveRingoidWithAntiDistribTerm A) → (ClInvolutiveRingoidWithAntiDistribTerm A)) 
  | (plusCl (primCl y) (primCl x)) := (primCl (plusCl x y))  
  | (timesCl (primCl y) (primCl x)) := (primCl (timesCl x y))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutiveRingoidWithAntiDistribTerm n) → (OpInvolutiveRingoidWithAntiDistribTerm n)) 
  | (plusOL (primOL y) (primOL x)) := (primOL (plusOL x y))  
  | (timesOL (primOL y) (primOL x)) := (primOL (timesOL x y))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) 
  | (plusOL2 (primOL2 y) (primOL2 x)) := (primOL2 (plusOL2 x y))  
  | (timesOL2 (primOL2 y) (primOL2 x)) := (primOL2 (timesOL2 x y))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveRingoidWithAntiDistrib A) → (InvolutiveRingoidWithAntiDistribTerm → A)) 
  | In (timesL x1 x2) := ((times In) (evalB In x1) (evalB In x2))  
  | In (plusL x1 x2) := ((plus In) (evalB In x1) (evalB In x2))  
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutiveRingoidWithAntiDistrib A) → ((ClInvolutiveRingoidWithAntiDistribTerm A) → A)) 
  | In (sing x1) := x1  
  | In (timesCl x1 x2) := ((times In) (evalCl In x1) (evalCl In x2))  
  | In (plusCl x1 x2) := ((plus In) (evalCl In x1) (evalCl In x2))  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutiveRingoidWithAntiDistrib A) → ((vector A n) → ((OpInvolutiveRingoidWithAntiDistribTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (timesOL x1 x2) := ((times In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (plusOL x1 x2) := ((plus In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutiveRingoidWithAntiDistrib A) → ((vector A n) → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (timesOL2 x1 x2) := ((times In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (plusOL2 x1 x2) := ((plus In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   (P : (InvolutiveRingoidWithAntiDistribTerm → Type))  : ((∀ (x1 x2 : InvolutiveRingoidWithAntiDistribTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : InvolutiveRingoidWithAntiDistribTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : InvolutiveRingoidWithAntiDistribTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutiveRingoidWithAntiDistribTerm) , (P x))))) 
  | ptimesl pplusl ppriml (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (primL x1) := (ppriml _ (inductionB ptimesl pplusl ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClInvolutiveRingoidWithAntiDistribTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClInvolutiveRingoidWithAntiDistribTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClInvolutiveRingoidWithAntiDistribTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClInvolutiveRingoidWithAntiDistribTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutiveRingoidWithAntiDistribTerm A)) , (P x)))))) 
  | psing ptimescl ppluscl pprimcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl pprimcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl ppluscl pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutiveRingoidWithAntiDistribTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpInvolutiveRingoidWithAntiDistribTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutiveRingoidWithAntiDistribTerm n)) , (P x)))))) 
  | pv ptimesol pplusol pprimol (v x1) := (pv x1)  
  | pv ptimesol pplusol pprimol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pplusol pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutiveRingoidWithAntiDistribTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1))  
  def stageB  : (InvolutiveRingoidWithAntiDistribTerm → (Staged InvolutiveRingoidWithAntiDistribTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClInvolutiveRingoidWithAntiDistribTerm A) → (Staged (ClInvolutiveRingoidWithAntiDistribTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpInvolutiveRingoidWithAntiDistribTerm n) → (Staged (OpInvolutiveRingoidWithAntiDistribTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A) → (Staged (OpInvolutiveRingoidWithAntiDistribTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end InvolutiveRingoidWithAntiDistrib