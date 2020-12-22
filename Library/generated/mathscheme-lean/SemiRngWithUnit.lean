import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section SemiRngWithUnit   
  structure SemiRngWithUnit  (A : Type) : Type := 
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open SemiRngWithUnit
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS)
       (plusS : (AS → (AS → AS)))
       (zeroS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Se1 : (SemiRngWithUnit A1)) (Se2 : (SemiRngWithUnit A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Se1) x1 x2)) = ((times Se2) (hom x1) (hom x2))))
       (pres_one : (hom (one Se1)) = (one Se2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Se1) x1 x2)) = ((plus Se2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Se1)) = (zero Se2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Se1 : (SemiRngWithUnit A1)) (Se2 : (SemiRngWithUnit A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Se1) x1 x2) ((times Se2) y1 y2))))))
       (interp_one : (interp (one Se1) (one Se2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Se1) x1 x2) ((plus Se2) y1 y2))))))
       (interp_zero : (interp (zero Se1) (zero Se2))) 
  
  inductive SemiRngWithUnitTerm   : Type  
     | timesL : (SemiRngWithUnitTerm → (SemiRngWithUnitTerm → SemiRngWithUnitTerm)) 
     | oneL : SemiRngWithUnitTerm 
     | plusL : (SemiRngWithUnitTerm → (SemiRngWithUnitTerm → SemiRngWithUnitTerm)) 
     | zeroL : SemiRngWithUnitTerm  
      open SemiRngWithUnitTerm 
  
  inductive ClSemiRngWithUnitTerm  (A : Type) : Type  
     | sing : (A → ClSemiRngWithUnitTerm) 
     | timesCl : (ClSemiRngWithUnitTerm → (ClSemiRngWithUnitTerm → ClSemiRngWithUnitTerm)) 
     | oneCl : ClSemiRngWithUnitTerm 
     | plusCl : (ClSemiRngWithUnitTerm → (ClSemiRngWithUnitTerm → ClSemiRngWithUnitTerm)) 
     | zeroCl : ClSemiRngWithUnitTerm  
      open ClSemiRngWithUnitTerm 
  
  inductive OpSemiRngWithUnitTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSemiRngWithUnitTerm) 
     | timesOL : (OpSemiRngWithUnitTerm → (OpSemiRngWithUnitTerm → OpSemiRngWithUnitTerm)) 
     | oneOL : OpSemiRngWithUnitTerm 
     | plusOL : (OpSemiRngWithUnitTerm → (OpSemiRngWithUnitTerm → OpSemiRngWithUnitTerm)) 
     | zeroOL : OpSemiRngWithUnitTerm  
      open OpSemiRngWithUnitTerm 
  
  inductive OpSemiRngWithUnitTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSemiRngWithUnitTerm2) 
     | sing2 : (A → OpSemiRngWithUnitTerm2) 
     | timesOL2 : (OpSemiRngWithUnitTerm2 → (OpSemiRngWithUnitTerm2 → OpSemiRngWithUnitTerm2)) 
     | oneOL2 : OpSemiRngWithUnitTerm2 
     | plusOL2 : (OpSemiRngWithUnitTerm2 → (OpSemiRngWithUnitTerm2 → OpSemiRngWithUnitTerm2)) 
     | zeroOL2 : OpSemiRngWithUnitTerm2  
      open OpSemiRngWithUnitTerm2 
  
  def simplifyCl   (A : Type)  : ((ClSemiRngWithUnitTerm A) → (ClSemiRngWithUnitTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpSemiRngWithUnitTerm n) → (OpSemiRngWithUnitTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpSemiRngWithUnitTerm2 n A) → (OpSemiRngWithUnitTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((SemiRngWithUnit A) → (SemiRngWithUnitTerm → A)) 
  | Se (timesL x1 x2) := ((times Se) (evalB Se x1) (evalB Se x2))  
  | Se oneL := (one Se)  
  | Se (plusL x1 x2) := ((plus Se) (evalB Se x1) (evalB Se x2))  
  | Se zeroL := (zero Se)  
  def evalCl   {A : Type}  : ((SemiRngWithUnit A) → ((ClSemiRngWithUnitTerm A) → A)) 
  | Se (sing x1) := x1  
  | Se (timesCl x1 x2) := ((times Se) (evalCl Se x1) (evalCl Se x2))  
  | Se oneCl := (one Se)  
  | Se (plusCl x1 x2) := ((plus Se) (evalCl Se x1) (evalCl Se x2))  
  | Se zeroCl := (zero Se)  
  def evalOpB   {A : Type} (n : ℕ)  : ((SemiRngWithUnit A) → ((vector A n) → ((OpSemiRngWithUnitTerm n) → A))) 
  | Se vars (v x1) := (nth vars x1)  
  | Se vars (timesOL x1 x2) := ((times Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  | Se vars oneOL := (one Se)  
  | Se vars (plusOL x1 x2) := ((plus Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  | Se vars zeroOL := (zero Se)  
  def evalOp   {A : Type} (n : ℕ)  : ((SemiRngWithUnit A) → ((vector A n) → ((OpSemiRngWithUnitTerm2 n A) → A))) 
  | Se vars (v2 x1) := (nth vars x1)  
  | Se vars (sing2 x1) := x1  
  | Se vars (timesOL2 x1 x2) := ((times Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  | Se vars oneOL2 := (one Se)  
  | Se vars (plusOL2 x1 x2) := ((plus Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  | Se vars zeroOL2 := (zero Se)  
  def inductionB   (P : (SemiRngWithUnitTerm → Type))  : ((∀ (x1 x2 : SemiRngWithUnitTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → ((∀ (x1 x2 : SemiRngWithUnitTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → (∀ (x : SemiRngWithUnitTerm) , (P x)))))) 
  | ptimesl p1l pplusl p0l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l pplusl p0l x1) (inductionB ptimesl p1l pplusl p0l x2))  
  | ptimesl p1l pplusl p0l oneL := p1l  
  | ptimesl p1l pplusl p0l (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl p1l pplusl p0l x1) (inductionB ptimesl p1l pplusl p0l x2))  
  | ptimesl p1l pplusl p0l zeroL := p0l  
  def inductionCl   (A : Type) (P : ((ClSemiRngWithUnitTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClSemiRngWithUnitTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → ((∀ (x1 x2 : (ClSemiRngWithUnitTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → (∀ (x : (ClSemiRngWithUnitTerm A)) , (P x))))))) 
  | psing ptimescl p1cl ppluscl p0cl (sing x1) := (psing x1)  
  | psing ptimescl p1cl ppluscl p0cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl ppluscl p0cl x1) (inductionCl psing ptimescl p1cl ppluscl p0cl x2))  
  | psing ptimescl p1cl ppluscl p0cl oneCl := p1cl  
  | psing ptimescl p1cl ppluscl p0cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl p1cl ppluscl p0cl x1) (inductionCl psing ptimescl p1cl ppluscl p0cl x2))  
  | psing ptimescl p1cl ppluscl p0cl zeroCl := p0cl  
  def inductionOpB   (n : ℕ) (P : ((OpSemiRngWithUnitTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpSemiRngWithUnitTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → ((∀ (x1 x2 : (OpSemiRngWithUnitTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → (∀ (x : (OpSemiRngWithUnitTerm n)) , (P x))))))) 
  | pv ptimesol p1ol pplusol p0ol (v x1) := (pv x1)  
  | pv ptimesol p1ol pplusol p0ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol pplusol p0ol x1) (inductionOpB pv ptimesol p1ol pplusol p0ol x2))  
  | pv ptimesol p1ol pplusol p0ol oneOL := p1ol  
  | pv ptimesol p1ol pplusol p0ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol p1ol pplusol p0ol x1) (inductionOpB pv ptimesol p1ol pplusol p0ol x2))  
  | pv ptimesol p1ol pplusol p0ol zeroOL := p0ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpSemiRngWithUnitTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpSemiRngWithUnitTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 x2 : (OpSemiRngWithUnitTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → (∀ (x : (OpSemiRngWithUnitTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 zeroOL2 := p0ol2  
  def stageB  : (SemiRngWithUnitTerm → (Staged SemiRngWithUnitTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  def stageCl   (A : Type)  : ((ClSemiRngWithUnitTerm A) → (Staged (ClSemiRngWithUnitTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  def stageOpB   (n : ℕ)  : ((OpSemiRngWithUnitTerm n) → (Staged (OpSemiRngWithUnitTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpSemiRngWithUnitTerm2 n A) → (Staged (OpSemiRngWithUnitTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A)) 
  
end SemiRngWithUnit