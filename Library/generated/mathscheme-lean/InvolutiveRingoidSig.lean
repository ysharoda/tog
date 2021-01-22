import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveRingoidSig   
  structure InvolutiveRingoidSig  (A : Type) : Type := 
       (prim : (A → A))
       (times : (A → (A → A)))
       (plus : (A → (A → A))) 
  
  open InvolutiveRingoidSig
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRingoidSig A1)) (In2 : (InvolutiveRingoidSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times In1) x1 x2)) = ((times In2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus In1) x1 x2)) = ((plus In2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRingoidSig A1)) (In2 : (InvolutiveRingoidSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times In1) x1 x2) ((times In2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus In1) x1 x2) ((plus In2) y1 y2)))))) 
  
  inductive InvolutiveRingoidSigTerm   : Type  
     | primL : (InvolutiveRingoidSigTerm → InvolutiveRingoidSigTerm) 
     | timesL : (InvolutiveRingoidSigTerm → (InvolutiveRingoidSigTerm → InvolutiveRingoidSigTerm)) 
     | plusL : (InvolutiveRingoidSigTerm → (InvolutiveRingoidSigTerm → InvolutiveRingoidSigTerm))  
      open InvolutiveRingoidSigTerm 
  
  inductive ClInvolutiveRingoidSigTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveRingoidSigTerm) 
     | primCl : (ClInvolutiveRingoidSigTerm → ClInvolutiveRingoidSigTerm) 
     | timesCl : (ClInvolutiveRingoidSigTerm → (ClInvolutiveRingoidSigTerm → ClInvolutiveRingoidSigTerm)) 
     | plusCl : (ClInvolutiveRingoidSigTerm → (ClInvolutiveRingoidSigTerm → ClInvolutiveRingoidSigTerm))  
      open ClInvolutiveRingoidSigTerm 
  
  inductive OpInvolutiveRingoidSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveRingoidSigTerm) 
     | primOL : (OpInvolutiveRingoidSigTerm → OpInvolutiveRingoidSigTerm) 
     | timesOL : (OpInvolutiveRingoidSigTerm → (OpInvolutiveRingoidSigTerm → OpInvolutiveRingoidSigTerm)) 
     | plusOL : (OpInvolutiveRingoidSigTerm → (OpInvolutiveRingoidSigTerm → OpInvolutiveRingoidSigTerm))  
      open OpInvolutiveRingoidSigTerm 
  
  inductive OpInvolutiveRingoidSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveRingoidSigTerm2) 
     | sing2 : (A → OpInvolutiveRingoidSigTerm2) 
     | primOL2 : (OpInvolutiveRingoidSigTerm2 → OpInvolutiveRingoidSigTerm2) 
     | timesOL2 : (OpInvolutiveRingoidSigTerm2 → (OpInvolutiveRingoidSigTerm2 → OpInvolutiveRingoidSigTerm2)) 
     | plusOL2 : (OpInvolutiveRingoidSigTerm2 → (OpInvolutiveRingoidSigTerm2 → OpInvolutiveRingoidSigTerm2))  
      open OpInvolutiveRingoidSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInvolutiveRingoidSigTerm A) → (ClInvolutiveRingoidSigTerm A)) 
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInvolutiveRingoidSigTerm n) → (OpInvolutiveRingoidSigTerm n)) 
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInvolutiveRingoidSigTerm2 n A) → (OpInvolutiveRingoidSigTerm2 n A)) 
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveRingoidSig A) → (InvolutiveRingoidSigTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In (timesL x1 x2) := ((times In) (evalB In x1) (evalB In x2))  
  | In (plusL x1 x2) := ((plus In) (evalB In x1) (evalB In x2))  
  def evalCl   {A : Type}  : ((InvolutiveRingoidSig A) → ((ClInvolutiveRingoidSigTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In (timesCl x1 x2) := ((times In) (evalCl In x1) (evalCl In x2))  
  | In (plusCl x1 x2) := ((plus In) (evalCl In x1) (evalCl In x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InvolutiveRingoidSig A) → ((vector A n) → ((OpInvolutiveRingoidSigTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars (timesOL x1 x2) := ((times In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (plusOL x1 x2) := ((plus In) (evalOpB In vars x1) (evalOpB In vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((InvolutiveRingoidSig A) → ((vector A n) → ((OpInvolutiveRingoidSigTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars (timesOL2 x1 x2) := ((times In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (plusOL2 x1 x2) := ((plus In) (evalOp In vars x1) (evalOp In vars x2))  
  def inductionB   {P : (InvolutiveRingoidSigTerm → Type)}  : ((∀ (x1 : InvolutiveRingoidSigTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : InvolutiveRingoidSigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : InvolutiveRingoidSigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : InvolutiveRingoidSigTerm) , (P x))))) 
  | ppriml ptimesl pplusl (primL x1) := (ppriml _ (inductionB ppriml ptimesl pplusl x1))  
  | ppriml ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ppriml ptimesl pplusl x1) (inductionB ppriml ptimesl pplusl x2))  
  | ppriml ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ppriml ptimesl pplusl x1) (inductionB ppriml ptimesl pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClInvolutiveRingoidSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutiveRingoidSigTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClInvolutiveRingoidSigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClInvolutiveRingoidSigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClInvolutiveRingoidSigTerm A)) , (P x)))))) 
  | psing pprimcl ptimescl ppluscl (sing x1) := (psing x1)  
  | psing pprimcl ptimescl ppluscl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl ptimescl ppluscl x1))  
  | psing pprimcl ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing pprimcl ptimescl ppluscl x1) (inductionCl psing pprimcl ptimescl ppluscl x2))  
  | psing pprimcl ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing pprimcl ptimescl ppluscl x1) (inductionCl psing pprimcl ptimescl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpInvolutiveRingoidSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutiveRingoidSigTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpInvolutiveRingoidSigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingoidSigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpInvolutiveRingoidSigTerm n)) , (P x)))))) 
  | pv pprimol ptimesol pplusol (v x1) := (pv x1)  
  | pv pprimol ptimesol pplusol (primOL x1) := (pprimol _ (inductionOpB pv pprimol ptimesol pplusol x1))  
  | pv pprimol ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pprimol ptimesol pplusol x1) (inductionOpB pv pprimol ptimesol pplusol x2))  
  | pv pprimol ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pprimol ptimesol pplusol x1) (inductionOpB pv pprimol ptimesol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInvolutiveRingoidSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutiveRingoidSigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpInvolutiveRingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpInvolutiveRingoidSigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pprimol2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 ptimesol2 pplusol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 ptimesol2 pplusol2 x1))  
  | pv2 psing2 pprimol2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pprimol2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 pprimol2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 pprimol2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pprimol2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 pprimol2 ptimesol2 pplusol2 x2))  
  def stageB  : (InvolutiveRingoidSigTerm → (Staged InvolutiveRingoidSigTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClInvolutiveRingoidSigTerm A) → (Staged (ClInvolutiveRingoidSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpInvolutiveRingoidSigTerm n) → (Staged (OpInvolutiveRingoidSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInvolutiveRingoidSigTerm2 n A) → (Staged (OpInvolutiveRingoidSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end InvolutiveRingoidSig