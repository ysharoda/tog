import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BoundedDistributiveLattice   
  structure BoundedDistributiveLattice  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (idempotent_times : (∀ {x : A} , (times x x) = x))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x))
       (leftAbsorp_times_plus : (∀ {x y : A} , (times x (plus x y)) = x))
       (leftAbsorp_plus_times : (∀ {x y : A} , (plus x (times x y)) = x))
       (leftModular_times_plus : (∀ {x y z : A} , (plus (times x y) (times x z)) = (times x (plus y (times x z)))))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z)))) 
  
  open BoundedDistributiveLattice
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (oneP : (Prod A A))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP))
       (leftAbsorp_times_plusP : (∀ {xP yP : (Prod A A)} , (timesP xP (plusP xP yP)) = xP))
       (leftAbsorp_plus_timesP : (∀ {xP yP : (Prod A A)} , (plusP xP (timesP xP yP)) = xP))
       (leftModular_times_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (timesP xP yP) (timesP xP zP)) = (timesP xP (plusP yP (timesP xP zP)))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BoundedDistributiveLattice A1)) (Bo2 : (BoundedDistributiveLattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Bo1) x1 x2)) = ((times Bo2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Bo1) x1 x2)) = ((plus Bo2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Bo1)) = (zero Bo2))
       (pres_one : (hom (one Bo1)) = (one Bo2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BoundedDistributiveLattice A1)) (Bo2 : (BoundedDistributiveLattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Bo1) x1 x2) ((times Bo2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Bo1) x1 x2) ((plus Bo2) y1 y2))))))
       (interp_zero : (interp (zero Bo1) (zero Bo2)))
       (interp_one : (interp (one Bo1) (one Bo2))) 
  
  inductive BoundedDistributiveLatticeTerm   : Type  
     | timesL : (BoundedDistributiveLatticeTerm → (BoundedDistributiveLatticeTerm → BoundedDistributiveLatticeTerm)) 
     | plusL : (BoundedDistributiveLatticeTerm → (BoundedDistributiveLatticeTerm → BoundedDistributiveLatticeTerm)) 
     | zeroL : BoundedDistributiveLatticeTerm 
     | oneL : BoundedDistributiveLatticeTerm  
      open BoundedDistributiveLatticeTerm 
  
  inductive ClBoundedDistributiveLatticeTerm  (A : Type) : Type  
     | sing : (A → ClBoundedDistributiveLatticeTerm) 
     | timesCl : (ClBoundedDistributiveLatticeTerm → (ClBoundedDistributiveLatticeTerm → ClBoundedDistributiveLatticeTerm)) 
     | plusCl : (ClBoundedDistributiveLatticeTerm → (ClBoundedDistributiveLatticeTerm → ClBoundedDistributiveLatticeTerm)) 
     | zeroCl : ClBoundedDistributiveLatticeTerm 
     | oneCl : ClBoundedDistributiveLatticeTerm  
      open ClBoundedDistributiveLatticeTerm 
  
  inductive OpBoundedDistributiveLatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBoundedDistributiveLatticeTerm) 
     | timesOL : (OpBoundedDistributiveLatticeTerm → (OpBoundedDistributiveLatticeTerm → OpBoundedDistributiveLatticeTerm)) 
     | plusOL : (OpBoundedDistributiveLatticeTerm → (OpBoundedDistributiveLatticeTerm → OpBoundedDistributiveLatticeTerm)) 
     | zeroOL : OpBoundedDistributiveLatticeTerm 
     | oneOL : OpBoundedDistributiveLatticeTerm  
      open OpBoundedDistributiveLatticeTerm 
  
  inductive OpBoundedDistributiveLatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBoundedDistributiveLatticeTerm2) 
     | sing2 : (A → OpBoundedDistributiveLatticeTerm2) 
     | timesOL2 : (OpBoundedDistributiveLatticeTerm2 → (OpBoundedDistributiveLatticeTerm2 → OpBoundedDistributiveLatticeTerm2)) 
     | plusOL2 : (OpBoundedDistributiveLatticeTerm2 → (OpBoundedDistributiveLatticeTerm2 → OpBoundedDistributiveLatticeTerm2)) 
     | zeroOL2 : OpBoundedDistributiveLatticeTerm2 
     | oneOL2 : OpBoundedDistributiveLatticeTerm2  
      open OpBoundedDistributiveLatticeTerm2 
  
  def simplifyCl   {A : Type}  : ((ClBoundedDistributiveLatticeTerm A) → (ClBoundedDistributiveLatticeTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpBoundedDistributiveLatticeTerm n) → (OpBoundedDistributiveLatticeTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpBoundedDistributiveLatticeTerm2 n A) → (OpBoundedDistributiveLatticeTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BoundedDistributiveLattice A) → (BoundedDistributiveLatticeTerm → A)) 
  | Bo (timesL x1 x2) := ((times Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo (plusL x1 x2) := ((plus Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo zeroL := (zero Bo)  
  | Bo oneL := (one Bo)  
  def evalCl   {A : Type}  : ((BoundedDistributiveLattice A) → ((ClBoundedDistributiveLatticeTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo (timesCl x1 x2) := ((times Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo (plusCl x1 x2) := ((plus Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo zeroCl := (zero Bo)  
  | Bo oneCl := (one Bo)  
  def evalOpB   {A : Type} {n : ℕ}  : ((BoundedDistributiveLattice A) → ((vector A n) → ((OpBoundedDistributiveLatticeTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars (timesOL x1 x2) := ((times Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars (plusOL x1 x2) := ((plus Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars zeroOL := (zero Bo)  
  | Bo vars oneOL := (one Bo)  
  def evalOp   {A : Type} {n : ℕ}  : ((BoundedDistributiveLattice A) → ((vector A n) → ((OpBoundedDistributiveLatticeTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars (timesOL2 x1 x2) := ((times Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars (plusOL2 x1 x2) := ((plus Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars zeroOL2 := (zero Bo)  
  | Bo vars oneOL2 := (one Bo)  
  def inductionB   {P : (BoundedDistributiveLatticeTerm → Type)}  : ((∀ (x1 x2 : BoundedDistributiveLatticeTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : BoundedDistributiveLatticeTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((P oneL) → (∀ (x : BoundedDistributiveLatticeTerm) , (P x)))))) 
  | ptimesl pplusl p0l p1l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p0l p1l x1) (inductionB ptimesl pplusl p0l p1l x2))  
  | ptimesl pplusl p0l p1l (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p0l p1l x1) (inductionB ptimesl pplusl p0l p1l x2))  
  | ptimesl pplusl p0l p1l zeroL := p0l  
  | ptimesl pplusl p0l p1l oneL := p1l  
  def inductionCl   {A : Type} {P : ((ClBoundedDistributiveLatticeTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBoundedDistributiveLatticeTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClBoundedDistributiveLatticeTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((P oneCl) → (∀ (x : (ClBoundedDistributiveLatticeTerm A)) , (P x))))))) 
  | psing ptimescl ppluscl p0cl p1cl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p0cl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p0cl p1cl x1) (inductionCl psing ptimescl ppluscl p0cl p1cl x2))  
  | psing ptimescl ppluscl p0cl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p0cl p1cl x1) (inductionCl psing ptimescl ppluscl p0cl p1cl x2))  
  | psing ptimescl ppluscl p0cl p1cl zeroCl := p0cl  
  | psing ptimescl ppluscl p0cl p1cl oneCl := p1cl  
  def inductionOpB   {n : ℕ} {P : ((OpBoundedDistributiveLatticeTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBoundedDistributiveLatticeTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpBoundedDistributiveLatticeTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((P oneOL) → (∀ (x : (OpBoundedDistributiveLatticeTerm n)) , (P x))))))) 
  | pv ptimesol pplusol p0ol p1ol (v x1) := (pv x1)  
  | pv ptimesol pplusol p0ol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p0ol p1ol x1) (inductionOpB pv ptimesol pplusol p0ol p1ol x2))  
  | pv ptimesol pplusol p0ol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p0ol p1ol x1) (inductionOpB pv ptimesol pplusol p0ol p1ol x2))  
  | pv ptimesol pplusol p0ol p1ol zeroOL := p0ol  
  | pv ptimesol pplusol p0ol p1ol oneOL := p1ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpBoundedDistributiveLatticeTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBoundedDistributiveLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpBoundedDistributiveLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((P oneOL2) → (∀ (x : (OpBoundedDistributiveLatticeTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (BoundedDistributiveLatticeTerm → (Staged BoundedDistributiveLatticeTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | oneL := (Now oneL)  
  def stageCl   {A : Type}  : ((ClBoundedDistributiveLatticeTerm A) → (Staged (ClBoundedDistributiveLatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | oneCl := (Now oneCl)  
  def stageOpB   {n : ℕ}  : ((OpBoundedDistributiveLatticeTerm n) → (Staged (OpBoundedDistributiveLatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | oneOL := (Now oneOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpBoundedDistributiveLatticeTerm2 n A) → (Staged (OpBoundedDistributiveLatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (oneT : (Repr A)) 
  
end BoundedDistributiveLattice