import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section NonassociativeNondistributiveRing   
  structure NonassociativeNondistributiveRing  (A : Type) : Type := 
       (times : (A → (A → A)))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (inv : (A → A))
       (leftInverse_inv_op_one : (∀ {x : A} , (times x (inv x)) = one))
       (rightInverse_inv_op_one : (∀ {x : A} , (times (inv x) x) = one))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (plus : (A → (A → A))) 
  
  open NonassociativeNondistributiveRing
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS)
       (invS : (AS → AS))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (invP : ((Prod A A) → (Prod A A)))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP xP (invP xP)) = oneP))
       (rightInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (timesP (invP xP) xP) = oneP))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (No1 : (NonassociativeNondistributiveRing A1)) (No2 : (NonassociativeNondistributiveRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times No1) x1 x2)) = ((times No2) (hom x1) (hom x2))))
       (pres_one : (hom (one No1)) = (one No2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv No1) x1)) = ((inv No2) (hom x1))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus No1) x1 x2)) = ((plus No2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (No1 : (NonassociativeNondistributiveRing A1)) (No2 : (NonassociativeNondistributiveRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times No1) x1 x2) ((times No2) y1 y2))))))
       (interp_one : (interp (one No1) (one No2)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv No1) x1) ((inv No2) y1)))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus No1) x1 x2) ((plus No2) y1 y2)))))) 
  
  inductive NonassociativeNondistributiveRingTerm   : Type  
     | timesL : (NonassociativeNondistributiveRingTerm → (NonassociativeNondistributiveRingTerm → NonassociativeNondistributiveRingTerm)) 
     | oneL : NonassociativeNondistributiveRingTerm 
     | invL : (NonassociativeNondistributiveRingTerm → NonassociativeNondistributiveRingTerm) 
     | plusL : (NonassociativeNondistributiveRingTerm → (NonassociativeNondistributiveRingTerm → NonassociativeNondistributiveRingTerm))  
      open NonassociativeNondistributiveRingTerm 
  
  inductive ClNonassociativeNondistributiveRingTerm  (A : Type) : Type  
     | sing : (A → ClNonassociativeNondistributiveRingTerm) 
     | timesCl : (ClNonassociativeNondistributiveRingTerm → (ClNonassociativeNondistributiveRingTerm → ClNonassociativeNondistributiveRingTerm)) 
     | oneCl : ClNonassociativeNondistributiveRingTerm 
     | invCl : (ClNonassociativeNondistributiveRingTerm → ClNonassociativeNondistributiveRingTerm) 
     | plusCl : (ClNonassociativeNondistributiveRingTerm → (ClNonassociativeNondistributiveRingTerm → ClNonassociativeNondistributiveRingTerm))  
      open ClNonassociativeNondistributiveRingTerm 
  
  inductive OpNonassociativeNondistributiveRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpNonassociativeNondistributiveRingTerm) 
     | timesOL : (OpNonassociativeNondistributiveRingTerm → (OpNonassociativeNondistributiveRingTerm → OpNonassociativeNondistributiveRingTerm)) 
     | oneOL : OpNonassociativeNondistributiveRingTerm 
     | invOL : (OpNonassociativeNondistributiveRingTerm → OpNonassociativeNondistributiveRingTerm) 
     | plusOL : (OpNonassociativeNondistributiveRingTerm → (OpNonassociativeNondistributiveRingTerm → OpNonassociativeNondistributiveRingTerm))  
      open OpNonassociativeNondistributiveRingTerm 
  
  inductive OpNonassociativeNondistributiveRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpNonassociativeNondistributiveRingTerm2) 
     | sing2 : (A → OpNonassociativeNondistributiveRingTerm2) 
     | timesOL2 : (OpNonassociativeNondistributiveRingTerm2 → (OpNonassociativeNondistributiveRingTerm2 → OpNonassociativeNondistributiveRingTerm2)) 
     | oneOL2 : OpNonassociativeNondistributiveRingTerm2 
     | invOL2 : (OpNonassociativeNondistributiveRingTerm2 → OpNonassociativeNondistributiveRingTerm2) 
     | plusOL2 : (OpNonassociativeNondistributiveRingTerm2 → (OpNonassociativeNondistributiveRingTerm2 → OpNonassociativeNondistributiveRingTerm2))  
      open OpNonassociativeNondistributiveRingTerm2 
  
  def simplifyCl   {A : Type}  : ((ClNonassociativeNondistributiveRingTerm A) → (ClNonassociativeNondistributiveRingTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpNonassociativeNondistributiveRingTerm n) → (OpNonassociativeNondistributiveRingTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpNonassociativeNondistributiveRingTerm2 n A) → (OpNonassociativeNondistributiveRingTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((NonassociativeNondistributiveRing A) → (NonassociativeNondistributiveRingTerm → A)) 
  | No (timesL x1 x2) := ((times No) (evalB No x1) (evalB No x2))  
  | No oneL := (one No)  
  | No (invL x1) := ((inv No) (evalB No x1))  
  | No (plusL x1 x2) := ((plus No) (evalB No x1) (evalB No x2))  
  def evalCl   {A : Type}  : ((NonassociativeNondistributiveRing A) → ((ClNonassociativeNondistributiveRingTerm A) → A)) 
  | No (sing x1) := x1  
  | No (timesCl x1 x2) := ((times No) (evalCl No x1) (evalCl No x2))  
  | No oneCl := (one No)  
  | No (invCl x1) := ((inv No) (evalCl No x1))  
  | No (plusCl x1 x2) := ((plus No) (evalCl No x1) (evalCl No x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((NonassociativeNondistributiveRing A) → ((vector A n) → ((OpNonassociativeNondistributiveRingTerm n) → A))) 
  | No vars (v x1) := (nth vars x1)  
  | No vars (timesOL x1 x2) := ((times No) (evalOpB No vars x1) (evalOpB No vars x2))  
  | No vars oneOL := (one No)  
  | No vars (invOL x1) := ((inv No) (evalOpB No vars x1))  
  | No vars (plusOL x1 x2) := ((plus No) (evalOpB No vars x1) (evalOpB No vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((NonassociativeNondistributiveRing A) → ((vector A n) → ((OpNonassociativeNondistributiveRingTerm2 n A) → A))) 
  | No vars (v2 x1) := (nth vars x1)  
  | No vars (sing2 x1) := x1  
  | No vars (timesOL2 x1 x2) := ((times No) (evalOp No vars x1) (evalOp No vars x2))  
  | No vars oneOL2 := (one No)  
  | No vars (invOL2 x1) := ((inv No) (evalOp No vars x1))  
  | No vars (plusOL2 x1 x2) := ((plus No) (evalOp No vars x1) (evalOp No vars x2))  
  def inductionB   {P : (NonassociativeNondistributiveRingTerm → Type)}  : ((∀ (x1 x2 : NonassociativeNondistributiveRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → ((∀ (x1 : NonassociativeNondistributiveRingTerm) , ((P x1) → (P (invL x1)))) → ((∀ (x1 x2 : NonassociativeNondistributiveRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : NonassociativeNondistributiveRingTerm) , (P x)))))) 
  | ptimesl p1l pinvl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l pinvl pplusl x1) (inductionB ptimesl p1l pinvl pplusl x2))  
  | ptimesl p1l pinvl pplusl oneL := p1l  
  | ptimesl p1l pinvl pplusl (invL x1) := (pinvl _ (inductionB ptimesl p1l pinvl pplusl x1))  
  | ptimesl p1l pinvl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl p1l pinvl pplusl x1) (inductionB ptimesl p1l pinvl pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClNonassociativeNondistributiveRingTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClNonassociativeNondistributiveRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → ((∀ (x1 : (ClNonassociativeNondistributiveRingTerm A)) , ((P x1) → (P (invCl x1)))) → ((∀ (x1 x2 : (ClNonassociativeNondistributiveRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClNonassociativeNondistributiveRingTerm A)) , (P x))))))) 
  | psing ptimescl p1cl pinvcl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl p1cl pinvcl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl pinvcl ppluscl x1) (inductionCl psing ptimescl p1cl pinvcl ppluscl x2))  
  | psing ptimescl p1cl pinvcl ppluscl oneCl := p1cl  
  | psing ptimescl p1cl pinvcl ppluscl (invCl x1) := (pinvcl _ (inductionCl psing ptimescl p1cl pinvcl ppluscl x1))  
  | psing ptimescl p1cl pinvcl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl p1cl pinvcl ppluscl x1) (inductionCl psing ptimescl p1cl pinvcl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpNonassociativeNondistributiveRingTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpNonassociativeNondistributiveRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → ((∀ (x1 : (OpNonassociativeNondistributiveRingTerm n)) , ((P x1) → (P (invOL x1)))) → ((∀ (x1 x2 : (OpNonassociativeNondistributiveRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpNonassociativeNondistributiveRingTerm n)) , (P x))))))) 
  | pv ptimesol p1ol pinvol pplusol (v x1) := (pv x1)  
  | pv ptimesol p1ol pinvol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol pinvol pplusol x1) (inductionOpB pv ptimesol p1ol pinvol pplusol x2))  
  | pv ptimesol p1ol pinvol pplusol oneOL := p1ol  
  | pv ptimesol p1ol pinvol pplusol (invOL x1) := (pinvol _ (inductionOpB pv ptimesol p1ol pinvol pplusol x1))  
  | pv ptimesol p1ol pinvol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol p1ol pinvol pplusol x1) (inductionOpB pv ptimesol p1ol pinvol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpNonassociativeNondistributiveRingTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpNonassociativeNondistributiveRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 : (OpNonassociativeNondistributiveRingTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → ((∀ (x1 x2 : (OpNonassociativeNondistributiveRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpNonassociativeNondistributiveRingTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 x1))  
  | pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pinvol2 pplusol2 x2))  
  def stageB  : (NonassociativeNondistributiveRingTerm → (Staged NonassociativeNondistributiveRingTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClNonassociativeNondistributiveRingTerm A) → (Staged (ClNonassociativeNondistributiveRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpNonassociativeNondistributiveRingTerm n) → (Staged (OpNonassociativeNondistributiveRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpNonassociativeNondistributiveRingTerm2 n A) → (Staged (OpNonassociativeNondistributiveRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (invT : ((Repr A) → (Repr A)))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end NonassociativeNondistributiveRing