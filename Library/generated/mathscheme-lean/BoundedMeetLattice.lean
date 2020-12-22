import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BoundedMeetLattice   
  structure BoundedMeetLattice  (A : Type) : Type := 
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (idempotent_times : (∀ {x : A} , (times x x) = x))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x))
       (leftAbsorp_times_plus : (∀ {x y : A} , (times x (plus x y)) = x))
       (leftAbsorp_plus_times : (∀ {x y : A} , (plus x (times x y)) = x)) 
  
  open BoundedMeetLattice
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS)
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP))
       (leftAbsorp_times_plusP : (∀ {xP yP : (Prod A A)} , (timesP xP (plusP xP yP)) = xP))
       (leftAbsorp_plus_timesP : (∀ {xP yP : (Prod A A)} , (plusP xP (timesP xP yP)) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BoundedMeetLattice A1)) (Bo2 : (BoundedMeetLattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Bo1) x1 x2)) = ((times Bo2) (hom x1) (hom x2))))
       (pres_one : (hom (one Bo1)) = (one Bo2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Bo1) x1 x2)) = ((plus Bo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BoundedMeetLattice A1)) (Bo2 : (BoundedMeetLattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Bo1) x1 x2) ((times Bo2) y1 y2))))))
       (interp_one : (interp (one Bo1) (one Bo2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Bo1) x1 x2) ((plus Bo2) y1 y2)))))) 
  
  inductive BoundedMeetLatticeTerm   : Type  
     | timesL : (BoundedMeetLatticeTerm → (BoundedMeetLatticeTerm → BoundedMeetLatticeTerm)) 
     | oneL : BoundedMeetLatticeTerm 
     | plusL : (BoundedMeetLatticeTerm → (BoundedMeetLatticeTerm → BoundedMeetLatticeTerm))  
      open BoundedMeetLatticeTerm 
  
  inductive ClBoundedMeetLatticeTerm  (A : Type) : Type  
     | sing : (A → ClBoundedMeetLatticeTerm) 
     | timesCl : (ClBoundedMeetLatticeTerm → (ClBoundedMeetLatticeTerm → ClBoundedMeetLatticeTerm)) 
     | oneCl : ClBoundedMeetLatticeTerm 
     | plusCl : (ClBoundedMeetLatticeTerm → (ClBoundedMeetLatticeTerm → ClBoundedMeetLatticeTerm))  
      open ClBoundedMeetLatticeTerm 
  
  inductive OpBoundedMeetLatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBoundedMeetLatticeTerm) 
     | timesOL : (OpBoundedMeetLatticeTerm → (OpBoundedMeetLatticeTerm → OpBoundedMeetLatticeTerm)) 
     | oneOL : OpBoundedMeetLatticeTerm 
     | plusOL : (OpBoundedMeetLatticeTerm → (OpBoundedMeetLatticeTerm → OpBoundedMeetLatticeTerm))  
      open OpBoundedMeetLatticeTerm 
  
  inductive OpBoundedMeetLatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBoundedMeetLatticeTerm2) 
     | sing2 : (A → OpBoundedMeetLatticeTerm2) 
     | timesOL2 : (OpBoundedMeetLatticeTerm2 → (OpBoundedMeetLatticeTerm2 → OpBoundedMeetLatticeTerm2)) 
     | oneOL2 : OpBoundedMeetLatticeTerm2 
     | plusOL2 : (OpBoundedMeetLatticeTerm2 → (OpBoundedMeetLatticeTerm2 → OpBoundedMeetLatticeTerm2))  
      open OpBoundedMeetLatticeTerm2 
  
  def simplifyCl   (A : Type)  : ((ClBoundedMeetLatticeTerm A) → (ClBoundedMeetLatticeTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpBoundedMeetLatticeTerm n) → (OpBoundedMeetLatticeTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpBoundedMeetLatticeTerm2 n A) → (OpBoundedMeetLatticeTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BoundedMeetLattice A) → (BoundedMeetLatticeTerm → A)) 
  | Bo (timesL x1 x2) := ((times Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo oneL := (one Bo)  
  | Bo (plusL x1 x2) := ((plus Bo) (evalB Bo x1) (evalB Bo x2))  
  def evalCl   {A : Type}  : ((BoundedMeetLattice A) → ((ClBoundedMeetLatticeTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo (timesCl x1 x2) := ((times Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo oneCl := (one Bo)  
  | Bo (plusCl x1 x2) := ((plus Bo) (evalCl Bo x1) (evalCl Bo x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((BoundedMeetLattice A) → ((vector A n) → ((OpBoundedMeetLatticeTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars (timesOL x1 x2) := ((times Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars oneOL := (one Bo)  
  | Bo vars (plusOL x1 x2) := ((plus Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((BoundedMeetLattice A) → ((vector A n) → ((OpBoundedMeetLatticeTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars (timesOL2 x1 x2) := ((times Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars oneOL2 := (one Bo)  
  | Bo vars (plusOL2 x1 x2) := ((plus Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  def inductionB   (P : (BoundedMeetLatticeTerm → Type))  : ((∀ (x1 x2 : BoundedMeetLatticeTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → ((∀ (x1 x2 : BoundedMeetLatticeTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : BoundedMeetLatticeTerm) , (P x))))) 
  | ptimesl p1l pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l pplusl x1) (inductionB ptimesl p1l pplusl x2))  
  | ptimesl p1l pplusl oneL := p1l  
  | ptimesl p1l pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl p1l pplusl x1) (inductionB ptimesl p1l pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClBoundedMeetLatticeTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBoundedMeetLatticeTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → ((∀ (x1 x2 : (ClBoundedMeetLatticeTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClBoundedMeetLatticeTerm A)) , (P x)))))) 
  | psing ptimescl p1cl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl p1cl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl ppluscl x1) (inductionCl psing ptimescl p1cl ppluscl x2))  
  | psing ptimescl p1cl ppluscl oneCl := p1cl  
  | psing ptimescl p1cl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl p1cl ppluscl x1) (inductionCl psing ptimescl p1cl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpBoundedMeetLatticeTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBoundedMeetLatticeTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → ((∀ (x1 x2 : (OpBoundedMeetLatticeTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpBoundedMeetLatticeTerm n)) , (P x)))))) 
  | pv ptimesol p1ol pplusol (v x1) := (pv x1)  
  | pv ptimesol p1ol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol pplusol x1) (inductionOpB pv ptimesol p1ol pplusol x2))  
  | pv ptimesol p1ol pplusol oneOL := p1ol  
  | pv ptimesol p1ol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol p1ol pplusol x1) (inductionOpB pv ptimesol p1ol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpBoundedMeetLatticeTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBoundedMeetLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 x2 : (OpBoundedMeetLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpBoundedMeetLatticeTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 x2))  
  def stageB  : (BoundedMeetLatticeTerm → (Staged BoundedMeetLatticeTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClBoundedMeetLatticeTerm A) → (Staged (ClBoundedMeetLatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpBoundedMeetLatticeTerm n) → (Staged (OpBoundedMeetLatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpBoundedMeetLatticeTerm2 n A) → (Staged (OpBoundedMeetLatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end BoundedMeetLattice