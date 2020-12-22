import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveRingoid   
  structure InvolutiveRingoid  (A : Type) : Type := 
       (prim : (A → A))
       (one : A)
       (fixes_prim_one : (prim one) = one)
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x))
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (antidis_prim_plus : (∀ {x y : A} , (prim (plus x y)) = (plus (prim y) (prim x))))
       (antidis_prim_times : (∀ {x y : A} , (prim (times x y)) = (times (prim y) (prim x)))) 
  
  open InvolutiveRingoid
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (oneS : AS)
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (oneP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (fixes_prim_1P : (primP oneP) = oneP)
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (antidis_prim_plusP : (∀ {xP yP : (Prod A A)} , (primP (plusP xP yP)) = (plusP (primP yP) (primP xP))))
       (antidis_prim_timesP : (∀ {xP yP : (Prod A A)} , (primP (timesP xP yP)) = (timesP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRingoid A1)) (In2 : (InvolutiveRingoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_one : (hom (one In1)) = (one In2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times In1) x1 x2)) = ((times In2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus In1) x1 x2)) = ((plus In2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRingoid A1)) (In2 : (InvolutiveRingoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_one : (interp (one In1) (one In2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times In1) x1 x2) ((times In2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus In1) x1 x2) ((plus In2) y1 y2)))))) 
  
  inductive InvolutiveRingoidTerm   : Type  
     | primL : (InvolutiveRingoidTerm → InvolutiveRingoidTerm) 
     | oneL : InvolutiveRingoidTerm 
     | timesL : (InvolutiveRingoidTerm → (InvolutiveRingoidTerm → InvolutiveRingoidTerm)) 
     | plusL : (InvolutiveRingoidTerm → (InvolutiveRingoidTerm → InvolutiveRingoidTerm))  
      open InvolutiveRingoidTerm 
  
  inductive ClInvolutiveRingoidTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveRingoidTerm) 
     | primCl : (ClInvolutiveRingoidTerm → ClInvolutiveRingoidTerm) 
     | oneCl : ClInvolutiveRingoidTerm 
     | timesCl : (ClInvolutiveRingoidTerm → (ClInvolutiveRingoidTerm → ClInvolutiveRingoidTerm)) 
     | plusCl : (ClInvolutiveRingoidTerm → (ClInvolutiveRingoidTerm → ClInvolutiveRingoidTerm))  
      open ClInvolutiveRingoidTerm 
  
  inductive OpInvolutiveRingoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveRingoidTerm) 
     | primOL : (OpInvolutiveRingoidTerm → OpInvolutiveRingoidTerm) 
     | oneOL : OpInvolutiveRingoidTerm 
     | timesOL : (OpInvolutiveRingoidTerm → (OpInvolutiveRingoidTerm → OpInvolutiveRingoidTerm)) 
     | plusOL : (OpInvolutiveRingoidTerm → (OpInvolutiveRingoidTerm → OpInvolutiveRingoidTerm))  
      open OpInvolutiveRingoidTerm 
  
  inductive OpInvolutiveRingoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveRingoidTerm2) 
     | sing2 : (A → OpInvolutiveRingoidTerm2) 
     | primOL2 : (OpInvolutiveRingoidTerm2 → OpInvolutiveRingoidTerm2) 
     | oneOL2 : OpInvolutiveRingoidTerm2 
     | timesOL2 : (OpInvolutiveRingoidTerm2 → (OpInvolutiveRingoidTerm2 → OpInvolutiveRingoidTerm2)) 
     | plusOL2 : (OpInvolutiveRingoidTerm2 → (OpInvolutiveRingoidTerm2 → OpInvolutiveRingoidTerm2))  
      open OpInvolutiveRingoidTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutiveRingoidTerm A) → (ClInvolutiveRingoidTerm A)) 
  | (primCl oneCl) := oneCl  
  | (primCl (primCl x)) := x  
  | (plusCl (primCl y) (primCl x)) := (primCl (plusCl x y))  
  | (timesCl (primCl y) (primCl x)) := (primCl (timesCl x y))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | oneCl := oneCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutiveRingoidTerm n) → (OpInvolutiveRingoidTerm n)) 
  | (primOL oneOL) := oneOL  
  | (primOL (primOL x)) := x  
  | (plusOL (primOL y) (primOL x)) := (primOL (plusOL x y))  
  | (timesOL (primOL y) (primOL x)) := (primOL (timesOL x y))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | oneOL := oneOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutiveRingoidTerm2 n A) → (OpInvolutiveRingoidTerm2 n A)) 
  | (primOL2 oneOL2) := oneOL2  
  | (primOL2 (primOL2 x)) := x  
  | (plusOL2 (primOL2 y) (primOL2 x)) := (primOL2 (plusOL2 x y))  
  | (timesOL2 (primOL2 y) (primOL2 x)) := (primOL2 (timesOL2 x y))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | oneOL2 := oneOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveRingoid A) → (InvolutiveRingoidTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In oneL := (one In)  
  | In (timesL x1 x2) := ((times In) (evalB In x1) (evalB In x2))  
  | In (plusL x1 x2) := ((plus In) (evalB In x1) (evalB In x2))  
  def evalCl   {A : Type}  : ((InvolutiveRingoid A) → ((ClInvolutiveRingoidTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In oneCl := (one In)  
  | In (timesCl x1 x2) := ((times In) (evalCl In x1) (evalCl In x2))  
  | In (plusCl x1 x2) := ((plus In) (evalCl In x1) (evalCl In x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutiveRingoid A) → ((vector A n) → ((OpInvolutiveRingoidTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars oneOL := (one In)  
  | In vars (timesOL x1 x2) := ((times In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (plusOL x1 x2) := ((plus In) (evalOpB In vars x1) (evalOpB In vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutiveRingoid A) → ((vector A n) → ((OpInvolutiveRingoidTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars oneOL2 := (one In)  
  | In vars (timesOL2 x1 x2) := ((times In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (plusOL2 x1 x2) := ((plus In) (evalOp In vars x1) (evalOp In vars x2))  
  def inductionB   (P : (InvolutiveRingoidTerm → Type))  : ((∀ (x1 : InvolutiveRingoidTerm) , ((P x1) → (P (primL x1)))) → ((P oneL) → ((∀ (x1 x2 : InvolutiveRingoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : InvolutiveRingoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : InvolutiveRingoidTerm) , (P x)))))) 
  | ppriml p1l ptimesl pplusl (primL x1) := (ppriml _ (inductionB ppriml p1l ptimesl pplusl x1))  
  | ppriml p1l ptimesl pplusl oneL := p1l  
  | ppriml p1l ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ppriml p1l ptimesl pplusl x1) (inductionB ppriml p1l ptimesl pplusl x2))  
  | ppriml p1l ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ppriml p1l ptimesl pplusl x1) (inductionB ppriml p1l ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClInvolutiveRingoidTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutiveRingoidTerm A)) , ((P x1) → (P (primCl x1)))) → ((P oneCl) → ((∀ (x1 x2 : (ClInvolutiveRingoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClInvolutiveRingoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClInvolutiveRingoidTerm A)) , (P x))))))) 
  | psing pprimcl p1cl ptimescl ppluscl (sing x1) := (psing x1)  
  | psing pprimcl p1cl ptimescl ppluscl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl p1cl ptimescl ppluscl x1))  
  | psing pprimcl p1cl ptimescl ppluscl oneCl := p1cl  
  | psing pprimcl p1cl ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing pprimcl p1cl ptimescl ppluscl x1) (inductionCl psing pprimcl p1cl ptimescl ppluscl x2))  
  | psing pprimcl p1cl ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing pprimcl p1cl ptimescl ppluscl x1) (inductionCl psing pprimcl p1cl ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutiveRingoidTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutiveRingoidTerm n)) , ((P x1) → (P (primOL x1)))) → ((P oneOL) → ((∀ (x1 x2 : (OpInvolutiveRingoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpInvolutiveRingoidTerm n)) , (P x))))))) 
  | pv pprimol p1ol ptimesol pplusol (v x1) := (pv x1)  
  | pv pprimol p1ol ptimesol pplusol (primOL x1) := (pprimol _ (inductionOpB pv pprimol p1ol ptimesol pplusol x1))  
  | pv pprimol p1ol ptimesol pplusol oneOL := p1ol  
  | pv pprimol p1ol ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pprimol p1ol ptimesol pplusol x1) (inductionOpB pv pprimol p1ol ptimesol pplusol x2))  
  | pv pprimol p1ol ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pprimol p1ol ptimesol pplusol x1) (inductionOpB pv pprimol p1ol ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutiveRingoidTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutiveRingoidTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P oneOL2) → ((∀ (x1 x2 : (OpInvolutiveRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpInvolutiveRingoidTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 x1))  
  | pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 oneOL2 := p1ol2  
  | pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 pprimol2 p1ol2 ptimesol2 pplusol2 x2))  
  def stageB  : (InvolutiveRingoidTerm → (Staged InvolutiveRingoidTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | oneL := (Now oneL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClInvolutiveRingoidTerm A) → (Staged (ClInvolutiveRingoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | oneCl := (Now oneCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpInvolutiveRingoidTerm n) → (Staged (OpInvolutiveRingoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | oneOL := (Now oneOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutiveRingoidTerm2 n A) → (Staged (OpInvolutiveRingoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | oneOL2 := (Now oneOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (oneT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end InvolutiveRingoid