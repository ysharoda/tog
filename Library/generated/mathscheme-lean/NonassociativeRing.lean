import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section NonassociativeRing   
  structure NonassociativeRing  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (inv : (A → A))
       (leftInverse_inv_op_one : (∀ {x : A} , (times x (inv x)) = one))
       (rightInverse_inv_op_one : (∀ {x : A} , (times (inv x) x) = one))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open NonassociativeRing
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (oneS : AS)
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (invP : ((Prod A A) → (Prod A A)))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP xP (invP xP)) = oneP))
       (rightInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP (invP xP) xP) = oneP))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (No1 : (NonassociativeRing A1)) (No2 : (NonassociativeRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times No1) x1 x2)) = ((times No2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus No1) x1 x2)) = ((plus No2) (hom x1) (hom x2))))
       (pres_one : (hom (one No1)) = (one No2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv No1) x1)) = ((inv No2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (No1 : (NonassociativeRing A1)) (No2 : (NonassociativeRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times No1) x1 x2) ((times No2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus No1) x1 x2) ((plus No2) y1 y2))))))
       (interp_one : (interp (one No1) (one No2)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv No1) x1) ((inv No2) y1))))) 
  
  inductive NonassociativeRingTerm   : Type  
     | timesL : (NonassociativeRingTerm → (NonassociativeRingTerm → NonassociativeRingTerm)) 
     | plusL : (NonassociativeRingTerm → (NonassociativeRingTerm → NonassociativeRingTerm)) 
     | oneL : NonassociativeRingTerm 
     | invL : (NonassociativeRingTerm → NonassociativeRingTerm)  
      open NonassociativeRingTerm 
  
  inductive ClNonassociativeRingTerm  (A : Type) : Type  
     | sing : (A → ClNonassociativeRingTerm) 
     | timesCl : (ClNonassociativeRingTerm → (ClNonassociativeRingTerm → ClNonassociativeRingTerm)) 
     | plusCl : (ClNonassociativeRingTerm → (ClNonassociativeRingTerm → ClNonassociativeRingTerm)) 
     | oneCl : ClNonassociativeRingTerm 
     | invCl : (ClNonassociativeRingTerm → ClNonassociativeRingTerm)  
      open ClNonassociativeRingTerm 
  
  inductive OpNonassociativeRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpNonassociativeRingTerm) 
     | timesOL : (OpNonassociativeRingTerm → (OpNonassociativeRingTerm → OpNonassociativeRingTerm)) 
     | plusOL : (OpNonassociativeRingTerm → (OpNonassociativeRingTerm → OpNonassociativeRingTerm)) 
     | oneOL : OpNonassociativeRingTerm 
     | invOL : (OpNonassociativeRingTerm → OpNonassociativeRingTerm)  
      open OpNonassociativeRingTerm 
  
  inductive OpNonassociativeRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpNonassociativeRingTerm2) 
     | sing2 : (A → OpNonassociativeRingTerm2) 
     | timesOL2 : (OpNonassociativeRingTerm2 → (OpNonassociativeRingTerm2 → OpNonassociativeRingTerm2)) 
     | plusOL2 : (OpNonassociativeRingTerm2 → (OpNonassociativeRingTerm2 → OpNonassociativeRingTerm2)) 
     | oneOL2 : OpNonassociativeRingTerm2 
     | invOL2 : (OpNonassociativeRingTerm2 → OpNonassociativeRingTerm2)  
      open OpNonassociativeRingTerm2 
  
  def simplifyCl   (A : Type)  : ((ClNonassociativeRingTerm A) → (ClNonassociativeRingTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpNonassociativeRingTerm n) → (OpNonassociativeRingTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpNonassociativeRingTerm2 n A) → (OpNonassociativeRingTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((NonassociativeRing A) → (NonassociativeRingTerm → A)) 
  | No (timesL x1 x2) := ((times No) (evalB No x1) (evalB No x2))  
  | No (plusL x1 x2) := ((plus No) (evalB No x1) (evalB No x2))  
  | No oneL := (one No)  
  | No (invL x1) := ((inv No) (evalB No x1))  
  def evalCl   {A : Type}  : ((NonassociativeRing A) → ((ClNonassociativeRingTerm A) → A)) 
  | No (sing x1) := x1  
  | No (timesCl x1 x2) := ((times No) (evalCl No x1) (evalCl No x2))  
  | No (plusCl x1 x2) := ((plus No) (evalCl No x1) (evalCl No x2))  
  | No oneCl := (one No)  
  | No (invCl x1) := ((inv No) (evalCl No x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((NonassociativeRing A) → ((vector A n) → ((OpNonassociativeRingTerm n) → A))) 
  | No vars (v x1) := (nth vars x1)  
  | No vars (timesOL x1 x2) := ((times No) (evalOpB No vars x1) (evalOpB No vars x2))  
  | No vars (plusOL x1 x2) := ((plus No) (evalOpB No vars x1) (evalOpB No vars x2))  
  | No vars oneOL := (one No)  
  | No vars (invOL x1) := ((inv No) (evalOpB No vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((NonassociativeRing A) → ((vector A n) → ((OpNonassociativeRingTerm2 n A) → A))) 
  | No vars (v2 x1) := (nth vars x1)  
  | No vars (sing2 x1) := x1  
  | No vars (timesOL2 x1 x2) := ((times No) (evalOp No vars x1) (evalOp No vars x2))  
  | No vars (plusOL2 x1 x2) := ((plus No) (evalOp No vars x1) (evalOp No vars x2))  
  | No vars oneOL2 := (one No)  
  | No vars (invOL2 x1) := ((inv No) (evalOp No vars x1))  
  def inductionB   (P : (NonassociativeRingTerm → Type))  : ((∀ (x1 x2 : NonassociativeRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : NonassociativeRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P oneL) → ((∀ (x1 : NonassociativeRingTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : NonassociativeRingTerm) , (P x)))))) 
  | ptimesl pplusl p1l pinvl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p1l pinvl x1) (inductionB ptimesl pplusl p1l pinvl x2))  
  | ptimesl pplusl p1l pinvl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p1l pinvl x1) (inductionB ptimesl pplusl p1l pinvl x2))  
  | ptimesl pplusl p1l pinvl oneL := p1l  
  | ptimesl pplusl p1l pinvl (invL x1) := (pinvl _ (inductionB ptimesl pplusl p1l pinvl x1))  
  def inductionCl   (A : Type) (P : ((ClNonassociativeRingTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClNonassociativeRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClNonassociativeRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P oneCl) → ((∀ (x1 : (ClNonassociativeRingTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClNonassociativeRingTerm A)) , (P x))))))) 
  | psing ptimescl ppluscl p1cl pinvcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p1cl pinvcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p1cl pinvcl x1) (inductionCl psing ptimescl ppluscl p1cl pinvcl x2))  
  | psing ptimescl ppluscl p1cl pinvcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p1cl pinvcl x1) (inductionCl psing ptimescl ppluscl p1cl pinvcl x2))  
  | psing ptimescl ppluscl p1cl pinvcl oneCl := p1cl  
  | psing ptimescl ppluscl p1cl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing ptimescl ppluscl p1cl pinvcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpNonassociativeRingTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpNonassociativeRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpNonassociativeRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P oneOL) → ((∀ (x1 : (OpNonassociativeRingTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpNonassociativeRingTerm n)) , (P x))))))) 
  | pv ptimesol pplusol p1ol pinvol (v x1) := (pv x1)  
  | pv ptimesol pplusol p1ol pinvol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p1ol pinvol x1) (inductionOpB pv ptimesol pplusol p1ol pinvol x2))  
  | pv ptimesol pplusol p1ol pinvol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p1ol pinvol x1) (inductionOpB pv ptimesol pplusol p1ol pinvol x2))  
  | pv ptimesol pplusol p1ol pinvol oneOL := p1ol  
  | pv ptimesol pplusol p1ol pinvol (invOL x1) := (pinvol _ (inductionOpB pv ptimesol pplusol p1ol pinvol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpNonassociativeRingTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpNonassociativeRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpNonassociativeRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 : (OpNonassociativeRingTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpNonassociativeRingTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pinvol2 x1))  
  def stageB  : (NonassociativeRingTerm → (Staged NonassociativeRingTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClNonassociativeRingTerm A) → (Staged (ClNonassociativeRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpNonassociativeRingTerm n) → (Staged (OpNonassociativeRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpNonassociativeRingTerm2 n A) → (Staged (OpNonassociativeRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (invT : ((Repr A) → (Repr A))) 
  
end NonassociativeRing