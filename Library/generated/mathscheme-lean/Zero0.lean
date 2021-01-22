import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Zero0   
  structure Zero0  (A : Type) : Type := 
       (zero : A)
       (times : (A → (A → A)))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero)) 
  
  open Zero0
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ze1 : (Zero0 A1)) (Ze2 : (Zero0 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ze1)) = (zero Ze2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ze1) x1 x2)) = ((times Ze2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ze1 : (Zero0 A1)) (Ze2 : (Zero0 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ze1) (zero Ze2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ze1) x1 x2) ((times Ze2) y1 y2)))))) 
  
  inductive Zero0LTerm   : Type  
     | zeroL : Zero0LTerm 
     | timesL : (Zero0LTerm → (Zero0LTerm → Zero0LTerm))  
      open Zero0LTerm 
  
  inductive ClZero0ClTerm  (A : Type) : Type  
     | sing : (A → ClZero0ClTerm) 
     | zeroCl : ClZero0ClTerm 
     | timesCl : (ClZero0ClTerm → (ClZero0ClTerm → ClZero0ClTerm))  
      open ClZero0ClTerm 
  
  inductive OpZero0OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpZero0OLTerm) 
     | zeroOL : OpZero0OLTerm 
     | timesOL : (OpZero0OLTerm → (OpZero0OLTerm → OpZero0OLTerm))  
      open OpZero0OLTerm 
  
  inductive OpZero0OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpZero0OL2Term2) 
     | sing2 : (A → OpZero0OL2Term2) 
     | zeroOL2 : OpZero0OL2Term2 
     | timesOL2 : (OpZero0OL2Term2 → (OpZero0OL2Term2 → OpZero0OL2Term2))  
      open OpZero0OL2Term2 
  
  def simplifyCl   {A : Type}  : ((ClZero0ClTerm A) → (ClZero0ClTerm A)) 
  | zeroCl := zeroCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpZero0OLTerm n) → (OpZero0OLTerm n)) 
  | zeroOL := zeroOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpZero0OL2Term2 n A) → (OpZero0OL2Term2 n A)) 
  | zeroOL2 := zeroOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Zero0 A) → (Zero0LTerm → A)) 
  | Ze zeroL := (zero Ze)  
  | Ze (timesL x1 x2) := ((times Ze) (evalB Ze x1) (evalB Ze x2))  
  def evalCl   {A : Type}  : ((Zero0 A) → ((ClZero0ClTerm A) → A)) 
  | Ze (sing x1) := x1  
  | Ze zeroCl := (zero Ze)  
  | Ze (timesCl x1 x2) := ((times Ze) (evalCl Ze x1) (evalCl Ze x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Zero0 A) → ((vector A n) → ((OpZero0OLTerm n) → A))) 
  | Ze vars (v x1) := (nth vars x1)  
  | Ze vars zeroOL := (zero Ze)  
  | Ze vars (timesOL x1 x2) := ((times Ze) (evalOpB Ze vars x1) (evalOpB Ze vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Zero0 A) → ((vector A n) → ((OpZero0OL2Term2 n A) → A))) 
  | Ze vars (v2 x1) := (nth vars x1)  
  | Ze vars (sing2 x1) := x1  
  | Ze vars zeroOL2 := (zero Ze)  
  | Ze vars (timesOL2 x1 x2) := ((times Ze) (evalOp Ze vars x1) (evalOp Ze vars x2))  
  def inductionB   {P : (Zero0LTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : Zero0LTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : Zero0LTerm) , (P x)))) 
  | p0l ptimesl zeroL := p0l  
  | p0l ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l ptimesl x1) (inductionB p0l ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClZero0ClTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClZero0ClTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClZero0ClTerm A)) , (P x))))) 
  | psing p0cl ptimescl (sing x1) := (psing x1)  
  | psing p0cl ptimescl zeroCl := p0cl  
  | psing p0cl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ptimescl x1) (inductionCl psing p0cl ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpZero0OLTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpZero0OLTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpZero0OLTerm n)) , (P x))))) 
  | pv p0ol ptimesol (v x1) := (pv x1)  
  | pv p0ol ptimesol zeroOL := p0ol  
  | pv p0ol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol ptimesol x1) (inductionOpB pv p0ol ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpZero0OL2Term2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpZero0OL2Term2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpZero0OL2Term2 n A)) , (P x)))))) 
  | pv2 psing2 p0ol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 ptimesol2 x2))  
  def stageB  : (Zero0LTerm → (Staged Zero0LTerm))
  | zeroL := (Now zeroL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClZero0ClTerm A) → (Staged (ClZero0ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpZero0OLTerm n) → (Staged (OpZero0OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpZero0OL2Term2 n A) → (Staged (OpZero0OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Zero0