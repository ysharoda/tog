import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BoundedMeetSemilattice   
  structure BoundedMeetSemilattice  (A : Type) : Type := 
       (times : (A → (A → A)))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (idempotent_times : (∀ {x : A} , (times x x) = x)) 
  
  open BoundedMeetSemilattice
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BoundedMeetSemilattice A1)) (Bo2 : (BoundedMeetSemilattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Bo1) x1 x2)) = ((times Bo2) (hom x1) (hom x2))))
       (pres_one : (hom (one Bo1)) = (one Bo2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BoundedMeetSemilattice A1)) (Bo2 : (BoundedMeetSemilattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Bo1) x1 x2) ((times Bo2) y1 y2))))))
       (interp_one : (interp (one Bo1) (one Bo2))) 
  
  inductive BoundedMeetSemilatticeTerm   : Type  
     | timesL : (BoundedMeetSemilatticeTerm → (BoundedMeetSemilatticeTerm → BoundedMeetSemilatticeTerm)) 
     | oneL : BoundedMeetSemilatticeTerm  
      open BoundedMeetSemilatticeTerm 
  
  inductive ClBoundedMeetSemilatticeTerm  (A : Type) : Type  
     | sing : (A → ClBoundedMeetSemilatticeTerm) 
     | timesCl : (ClBoundedMeetSemilatticeTerm → (ClBoundedMeetSemilatticeTerm → ClBoundedMeetSemilatticeTerm)) 
     | oneCl : ClBoundedMeetSemilatticeTerm  
      open ClBoundedMeetSemilatticeTerm 
  
  inductive OpBoundedMeetSemilatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBoundedMeetSemilatticeTerm) 
     | timesOL : (OpBoundedMeetSemilatticeTerm → (OpBoundedMeetSemilatticeTerm → OpBoundedMeetSemilatticeTerm)) 
     | oneOL : OpBoundedMeetSemilatticeTerm  
      open OpBoundedMeetSemilatticeTerm 
  
  inductive OpBoundedMeetSemilatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBoundedMeetSemilatticeTerm2) 
     | sing2 : (A → OpBoundedMeetSemilatticeTerm2) 
     | timesOL2 : (OpBoundedMeetSemilatticeTerm2 → (OpBoundedMeetSemilatticeTerm2 → OpBoundedMeetSemilatticeTerm2)) 
     | oneOL2 : OpBoundedMeetSemilatticeTerm2  
      open OpBoundedMeetSemilatticeTerm2 
  
  def simplifyCl   {A : Type}  : ((ClBoundedMeetSemilatticeTerm A) → (ClBoundedMeetSemilatticeTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpBoundedMeetSemilatticeTerm n) → (OpBoundedMeetSemilatticeTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpBoundedMeetSemilatticeTerm2 n A) → (OpBoundedMeetSemilatticeTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BoundedMeetSemilattice A) → (BoundedMeetSemilatticeTerm → A)) 
  | Bo (timesL x1 x2) := ((times Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo oneL := (one Bo)  
  def evalCl   {A : Type}  : ((BoundedMeetSemilattice A) → ((ClBoundedMeetSemilatticeTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo (timesCl x1 x2) := ((times Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo oneCl := (one Bo)  
  def evalOpB   {A : Type} {n : ℕ}  : ((BoundedMeetSemilattice A) → ((vector A n) → ((OpBoundedMeetSemilatticeTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars (timesOL x1 x2) := ((times Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars oneOL := (one Bo)  
  def evalOp   {A : Type} {n : ℕ}  : ((BoundedMeetSemilattice A) → ((vector A n) → ((OpBoundedMeetSemilatticeTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars (timesOL2 x1 x2) := ((times Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars oneOL2 := (one Bo)  
  def inductionB   {P : (BoundedMeetSemilatticeTerm → Type)}  : ((∀ (x1 x2 : BoundedMeetSemilatticeTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → (∀ (x : BoundedMeetSemilatticeTerm) , (P x)))) 
  | ptimesl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l x1) (inductionB ptimesl p1l x2))  
  | ptimesl p1l oneL := p1l  
  def inductionCl   {A : Type} {P : ((ClBoundedMeetSemilatticeTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBoundedMeetSemilatticeTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → (∀ (x : (ClBoundedMeetSemilatticeTerm A)) , (P x))))) 
  | psing ptimescl p1cl (sing x1) := (psing x1)  
  | psing ptimescl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl x1) (inductionCl psing ptimescl p1cl x2))  
  | psing ptimescl p1cl oneCl := p1cl  
  def inductionOpB   {n : ℕ} {P : ((OpBoundedMeetSemilatticeTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBoundedMeetSemilatticeTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → (∀ (x : (OpBoundedMeetSemilatticeTerm n)) , (P x))))) 
  | pv ptimesol p1ol (v x1) := (pv x1)  
  | pv ptimesol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol x1) (inductionOpB pv ptimesol p1ol x2))  
  | pv ptimesol p1ol oneOL := p1ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpBoundedMeetSemilatticeTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBoundedMeetSemilatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → (∀ (x : (OpBoundedMeetSemilatticeTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (BoundedMeetSemilatticeTerm → (Staged BoundedMeetSemilatticeTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  def stageCl   {A : Type}  : ((ClBoundedMeetSemilatticeTerm A) → (Staged (ClBoundedMeetSemilatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  def stageOpB   {n : ℕ}  : ((OpBoundedMeetSemilatticeTerm n) → (Staged (OpBoundedMeetSemilatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpBoundedMeetSemilatticeTerm2 n A) → (Staged (OpBoundedMeetSemilatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A)) 
  
end BoundedMeetSemilattice