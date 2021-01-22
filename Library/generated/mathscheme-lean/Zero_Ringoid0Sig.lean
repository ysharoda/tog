import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Zero_Ringoid0Sig   
  structure Zero_Ringoid0Sig  (A : Type) : Type := 
       (zero : A)
       (times : (A → (A → A)))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero))
       (plus : (A → (A → A))) 
  
  open Zero_Ringoid0Sig
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ze1 : (Zero_Ringoid0Sig A1)) (Ze2 : (Zero_Ringoid0Sig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ze1)) = (zero Ze2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ze1) x1 x2)) = ((times Ze2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ze1) x1 x2)) = ((plus Ze2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ze1 : (Zero_Ringoid0Sig A1)) (Ze2 : (Zero_Ringoid0Sig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ze1) (zero Ze2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ze1) x1 x2) ((times Ze2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ze1) x1 x2) ((plus Ze2) y1 y2)))))) 
  
  inductive Zero_Ringoid0SigTerm   : Type  
     | zeroL : Zero_Ringoid0SigTerm 
     | timesL : (Zero_Ringoid0SigTerm → (Zero_Ringoid0SigTerm → Zero_Ringoid0SigTerm)) 
     | plusL : (Zero_Ringoid0SigTerm → (Zero_Ringoid0SigTerm → Zero_Ringoid0SigTerm))  
      open Zero_Ringoid0SigTerm 
  
  inductive ClZero_Ringoid0SigTerm  (A : Type) : Type  
     | sing : (A → ClZero_Ringoid0SigTerm) 
     | zeroCl : ClZero_Ringoid0SigTerm 
     | timesCl : (ClZero_Ringoid0SigTerm → (ClZero_Ringoid0SigTerm → ClZero_Ringoid0SigTerm)) 
     | plusCl : (ClZero_Ringoid0SigTerm → (ClZero_Ringoid0SigTerm → ClZero_Ringoid0SigTerm))  
      open ClZero_Ringoid0SigTerm 
  
  inductive OpZero_Ringoid0SigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpZero_Ringoid0SigTerm) 
     | zeroOL : OpZero_Ringoid0SigTerm 
     | timesOL : (OpZero_Ringoid0SigTerm → (OpZero_Ringoid0SigTerm → OpZero_Ringoid0SigTerm)) 
     | plusOL : (OpZero_Ringoid0SigTerm → (OpZero_Ringoid0SigTerm → OpZero_Ringoid0SigTerm))  
      open OpZero_Ringoid0SigTerm 
  
  inductive OpZero_Ringoid0SigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpZero_Ringoid0SigTerm2) 
     | sing2 : (A → OpZero_Ringoid0SigTerm2) 
     | zeroOL2 : OpZero_Ringoid0SigTerm2 
     | timesOL2 : (OpZero_Ringoid0SigTerm2 → (OpZero_Ringoid0SigTerm2 → OpZero_Ringoid0SigTerm2)) 
     | plusOL2 : (OpZero_Ringoid0SigTerm2 → (OpZero_Ringoid0SigTerm2 → OpZero_Ringoid0SigTerm2))  
      open OpZero_Ringoid0SigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClZero_Ringoid0SigTerm A) → (ClZero_Ringoid0SigTerm A)) 
  | zeroCl := zeroCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpZero_Ringoid0SigTerm n) → (OpZero_Ringoid0SigTerm n)) 
  | zeroOL := zeroOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpZero_Ringoid0SigTerm2 n A) → (OpZero_Ringoid0SigTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Zero_Ringoid0Sig A) → (Zero_Ringoid0SigTerm → A)) 
  | Ze zeroL := (zero Ze)  
  | Ze (timesL x1 x2) := ((times Ze) (evalB Ze x1) (evalB Ze x2))  
  | Ze (plusL x1 x2) := ((plus Ze) (evalB Ze x1) (evalB Ze x2))  
  def evalCl   {A : Type}  : ((Zero_Ringoid0Sig A) → ((ClZero_Ringoid0SigTerm A) → A)) 
  | Ze (sing x1) := x1  
  | Ze zeroCl := (zero Ze)  
  | Ze (timesCl x1 x2) := ((times Ze) (evalCl Ze x1) (evalCl Ze x2))  
  | Ze (plusCl x1 x2) := ((plus Ze) (evalCl Ze x1) (evalCl Ze x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Zero_Ringoid0Sig A) → ((vector A n) → ((OpZero_Ringoid0SigTerm n) → A))) 
  | Ze vars (v x1) := (nth vars x1)  
  | Ze vars zeroOL := (zero Ze)  
  | Ze vars (timesOL x1 x2) := ((times Ze) (evalOpB Ze vars x1) (evalOpB Ze vars x2))  
  | Ze vars (plusOL x1 x2) := ((plus Ze) (evalOpB Ze vars x1) (evalOpB Ze vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Zero_Ringoid0Sig A) → ((vector A n) → ((OpZero_Ringoid0SigTerm2 n A) → A))) 
  | Ze vars (v2 x1) := (nth vars x1)  
  | Ze vars (sing2 x1) := x1  
  | Ze vars zeroOL2 := (zero Ze)  
  | Ze vars (timesOL2 x1 x2) := ((times Ze) (evalOp Ze vars x1) (evalOp Ze vars x2))  
  | Ze vars (plusOL2 x1 x2) := ((plus Ze) (evalOp Ze vars x1) (evalOp Ze vars x2))  
  def inductionB   {P : (Zero_Ringoid0SigTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : Zero_Ringoid0SigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : Zero_Ringoid0SigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : Zero_Ringoid0SigTerm) , (P x))))) 
  | p0l ptimesl pplusl zeroL := p0l  
  | p0l ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l ptimesl pplusl x1) (inductionB p0l ptimesl pplusl x2))  
  | p0l ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB p0l ptimesl pplusl x1) (inductionB p0l ptimesl pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClZero_Ringoid0SigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClZero_Ringoid0SigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClZero_Ringoid0SigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClZero_Ringoid0SigTerm A)) , (P x)))))) 
  | psing p0cl ptimescl ppluscl (sing x1) := (psing x1)  
  | psing p0cl ptimescl ppluscl zeroCl := p0cl  
  | psing p0cl ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ptimescl ppluscl x1) (inductionCl psing p0cl ptimescl ppluscl x2))  
  | psing p0cl ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ptimescl ppluscl x1) (inductionCl psing p0cl ptimescl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpZero_Ringoid0SigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpZero_Ringoid0SigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpZero_Ringoid0SigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpZero_Ringoid0SigTerm n)) , (P x)))))) 
  | pv p0ol ptimesol pplusol (v x1) := (pv x1)  
  | pv p0ol ptimesol pplusol zeroOL := p0ol  
  | pv p0ol ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol ptimesol pplusol x1) (inductionOpB pv p0ol ptimesol pplusol x2))  
  | pv p0ol ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol ptimesol pplusol x1) (inductionOpB pv p0ol ptimesol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpZero_Ringoid0SigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpZero_Ringoid0SigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpZero_Ringoid0SigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpZero_Ringoid0SigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 p0ol2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 ptimesol2 pplusol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 p0ol2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 p0ol2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 p0ol2 ptimesol2 pplusol2 x2))  
  def stageB  : (Zero_Ringoid0SigTerm → (Staged Zero_Ringoid0SigTerm))
  | zeroL := (Now zeroL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClZero_Ringoid0SigTerm A) → (Staged (ClZero_Ringoid0SigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpZero_Ringoid0SigTerm n) → (Staged (OpZero_Ringoid0SigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpZero_Ringoid0SigTerm2 n A) → (Staged (OpZero_Ringoid0SigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Zero_Ringoid0Sig