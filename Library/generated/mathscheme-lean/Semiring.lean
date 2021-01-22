import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Semiring   
  structure Semiring  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero)) 
  
  open Semiring
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS)))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Se1 : (Semiring A1)) (Se2 : (Semiring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Se1)) = (zero Se2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Se1) x1 x2)) = ((plus Se2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Se1) x1 x2)) = ((times Se2) (hom x1) (hom x2))))
       (pres_one : (hom (one Se1)) = (one Se2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Se1 : (Semiring A1)) (Se2 : (Semiring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Se1) (zero Se2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Se1) x1 x2) ((plus Se2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Se1) x1 x2) ((times Se2) y1 y2))))))
       (interp_one : (interp (one Se1) (one Se2))) 
  
  inductive SemiringTerm   : Type  
     | zeroL : SemiringTerm 
     | plusL : (SemiringTerm → (SemiringTerm → SemiringTerm)) 
     | timesL : (SemiringTerm → (SemiringTerm → SemiringTerm)) 
     | oneL : SemiringTerm  
      open SemiringTerm 
  
  inductive ClSemiringTerm  (A : Type) : Type  
     | sing : (A → ClSemiringTerm) 
     | zeroCl : ClSemiringTerm 
     | plusCl : (ClSemiringTerm → (ClSemiringTerm → ClSemiringTerm)) 
     | timesCl : (ClSemiringTerm → (ClSemiringTerm → ClSemiringTerm)) 
     | oneCl : ClSemiringTerm  
      open ClSemiringTerm 
  
  inductive OpSemiringTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSemiringTerm) 
     | zeroOL : OpSemiringTerm 
     | plusOL : (OpSemiringTerm → (OpSemiringTerm → OpSemiringTerm)) 
     | timesOL : (OpSemiringTerm → (OpSemiringTerm → OpSemiringTerm)) 
     | oneOL : OpSemiringTerm  
      open OpSemiringTerm 
  
  inductive OpSemiringTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSemiringTerm2) 
     | sing2 : (A → OpSemiringTerm2) 
     | zeroOL2 : OpSemiringTerm2 
     | plusOL2 : (OpSemiringTerm2 → (OpSemiringTerm2 → OpSemiringTerm2)) 
     | timesOL2 : (OpSemiringTerm2 → (OpSemiringTerm2 → OpSemiringTerm2)) 
     | oneOL2 : OpSemiringTerm2  
      open OpSemiringTerm2 
  
  def simplifyCl   {A : Type}  : ((ClSemiringTerm A) → (ClSemiringTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpSemiringTerm n) → (OpSemiringTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpSemiringTerm2 n A) → (OpSemiringTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Semiring A) → (SemiringTerm → A)) 
  | Se zeroL := (zero Se)  
  | Se (plusL x1 x2) := ((plus Se) (evalB Se x1) (evalB Se x2))  
  | Se (timesL x1 x2) := ((times Se) (evalB Se x1) (evalB Se x2))  
  | Se oneL := (one Se)  
  def evalCl   {A : Type}  : ((Semiring A) → ((ClSemiringTerm A) → A)) 
  | Se (sing x1) := x1  
  | Se zeroCl := (zero Se)  
  | Se (plusCl x1 x2) := ((plus Se) (evalCl Se x1) (evalCl Se x2))  
  | Se (timesCl x1 x2) := ((times Se) (evalCl Se x1) (evalCl Se x2))  
  | Se oneCl := (one Se)  
  def evalOpB   {A : Type} {n : ℕ}  : ((Semiring A) → ((vector A n) → ((OpSemiringTerm n) → A))) 
  | Se vars (v x1) := (nth vars x1)  
  | Se vars zeroOL := (zero Se)  
  | Se vars (plusOL x1 x2) := ((plus Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  | Se vars (timesOL x1 x2) := ((times Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  | Se vars oneOL := (one Se)  
  def evalOp   {A : Type} {n : ℕ}  : ((Semiring A) → ((vector A n) → ((OpSemiringTerm2 n A) → A))) 
  | Se vars (v2 x1) := (nth vars x1)  
  | Se vars (sing2 x1) := x1  
  | Se vars zeroOL2 := (zero Se)  
  | Se vars (plusOL2 x1 x2) := ((plus Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  | Se vars (timesOL2 x1 x2) := ((times Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  | Se vars oneOL2 := (one Se)  
  def inductionB   {P : (SemiringTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : SemiringTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : SemiringTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → (∀ (x : SemiringTerm) , (P x)))))) 
  | p0l pplusl ptimesl p1l zeroL := p0l  
  | p0l pplusl ptimesl p1l (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl ptimesl p1l x1) (inductionB p0l pplusl ptimesl p1l x2))  
  | p0l pplusl ptimesl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB p0l pplusl ptimesl p1l x1) (inductionB p0l pplusl ptimesl p1l x2))  
  | p0l pplusl ptimesl p1l oneL := p1l  
  def inductionCl   {A : Type} {P : ((ClSemiringTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClSemiringTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClSemiringTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → (∀ (x : (ClSemiringTerm A)) , (P x))))))) 
  | psing p0cl ppluscl ptimescl p1cl (sing x1) := (psing x1)  
  | psing p0cl ppluscl ptimescl p1cl zeroCl := p0cl  
  | psing p0cl ppluscl ptimescl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl ptimescl p1cl x1) (inductionCl psing p0cl ppluscl ptimescl p1cl x2))  
  | psing p0cl ppluscl ptimescl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ppluscl ptimescl p1cl x1) (inductionCl psing p0cl ppluscl ptimescl p1cl x2))  
  | psing p0cl ppluscl ptimescl p1cl oneCl := p1cl  
  def inductionOpB   {n : ℕ} {P : ((OpSemiringTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpSemiringTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpSemiringTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → (∀ (x : (OpSemiringTerm n)) , (P x))))))) 
  | pv p0ol pplusol ptimesol p1ol (v x1) := (pv x1)  
  | pv p0ol pplusol ptimesol p1ol zeroOL := p0ol  
  | pv p0ol pplusol ptimesol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol ptimesol p1ol x1) (inductionOpB pv p0ol pplusol ptimesol p1ol x2))  
  | pv p0ol pplusol ptimesol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol pplusol ptimesol p1ol x1) (inductionOpB pv p0ol pplusol ptimesol p1ol x2))  
  | pv p0ol pplusol ptimesol p1ol oneOL := p1ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpSemiringTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → (∀ (x : (OpSemiringTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (SemiringTerm → (Staged SemiringTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  def stageCl   {A : Type}  : ((ClSemiringTerm A) → (Staged (ClSemiringTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  def stageOpB   {n : ℕ}  : ((OpSemiringTerm n) → (Staged (OpSemiringTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpSemiringTerm2 n A) → (Staged (OpSemiringTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A)) 
  
end Semiring