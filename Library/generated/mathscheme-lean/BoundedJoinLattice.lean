import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BoundedJoinLattice   
  structure BoundedJoinLattice  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (times : (A → (A → A)))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (idempotent_times : (∀ {x : A} , (times x x) = x))
       (leftAbsorp_times_plus : (∀ {x y : A} , (times x (plus x y)) = x))
       (leftAbsorp_plus_times : (∀ {x y : A} , (plus x (times x y)) = x)) 
  
  open BoundedJoinLattice
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP))
       (leftAbsorp_times_plusP : (∀ {xP yP : (Prod A A)} , (timesP xP (plusP xP yP)) = xP))
       (leftAbsorp_plus_timesP : (∀ {xP yP : (Prod A A)} , (plusP xP (timesP xP yP)) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BoundedJoinLattice A1)) (Bo2 : (BoundedJoinLattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Bo1) x1 x2)) = ((plus Bo2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Bo1)) = (zero Bo2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Bo1) x1 x2)) = ((times Bo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BoundedJoinLattice A1)) (Bo2 : (BoundedJoinLattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Bo1) x1 x2) ((plus Bo2) y1 y2))))))
       (interp_zero : (interp (zero Bo1) (zero Bo2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Bo1) x1 x2) ((times Bo2) y1 y2)))))) 
  
  inductive BoundedJoinLatticeTerm   : Type  
     | plusL : (BoundedJoinLatticeTerm → (BoundedJoinLatticeTerm → BoundedJoinLatticeTerm)) 
     | zeroL : BoundedJoinLatticeTerm 
     | timesL : (BoundedJoinLatticeTerm → (BoundedJoinLatticeTerm → BoundedJoinLatticeTerm))  
      open BoundedJoinLatticeTerm 
  
  inductive ClBoundedJoinLatticeTerm  (A : Type) : Type  
     | sing : (A → ClBoundedJoinLatticeTerm) 
     | plusCl : (ClBoundedJoinLatticeTerm → (ClBoundedJoinLatticeTerm → ClBoundedJoinLatticeTerm)) 
     | zeroCl : ClBoundedJoinLatticeTerm 
     | timesCl : (ClBoundedJoinLatticeTerm → (ClBoundedJoinLatticeTerm → ClBoundedJoinLatticeTerm))  
      open ClBoundedJoinLatticeTerm 
  
  inductive OpBoundedJoinLatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBoundedJoinLatticeTerm) 
     | plusOL : (OpBoundedJoinLatticeTerm → (OpBoundedJoinLatticeTerm → OpBoundedJoinLatticeTerm)) 
     | zeroOL : OpBoundedJoinLatticeTerm 
     | timesOL : (OpBoundedJoinLatticeTerm → (OpBoundedJoinLatticeTerm → OpBoundedJoinLatticeTerm))  
      open OpBoundedJoinLatticeTerm 
  
  inductive OpBoundedJoinLatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBoundedJoinLatticeTerm2) 
     | sing2 : (A → OpBoundedJoinLatticeTerm2) 
     | plusOL2 : (OpBoundedJoinLatticeTerm2 → (OpBoundedJoinLatticeTerm2 → OpBoundedJoinLatticeTerm2)) 
     | zeroOL2 : OpBoundedJoinLatticeTerm2 
     | timesOL2 : (OpBoundedJoinLatticeTerm2 → (OpBoundedJoinLatticeTerm2 → OpBoundedJoinLatticeTerm2))  
      open OpBoundedJoinLatticeTerm2 
  
  def simplifyCl   (A : Type)  : ((ClBoundedJoinLatticeTerm A) → (ClBoundedJoinLatticeTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpBoundedJoinLatticeTerm n) → (OpBoundedJoinLatticeTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpBoundedJoinLatticeTerm2 n A) → (OpBoundedJoinLatticeTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BoundedJoinLattice A) → (BoundedJoinLatticeTerm → A)) 
  | Bo (plusL x1 x2) := ((plus Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo zeroL := (zero Bo)  
  | Bo (timesL x1 x2) := ((times Bo) (evalB Bo x1) (evalB Bo x2))  
  def evalCl   {A : Type}  : ((BoundedJoinLattice A) → ((ClBoundedJoinLatticeTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo (plusCl x1 x2) := ((plus Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo zeroCl := (zero Bo)  
  | Bo (timesCl x1 x2) := ((times Bo) (evalCl Bo x1) (evalCl Bo x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((BoundedJoinLattice A) → ((vector A n) → ((OpBoundedJoinLatticeTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars (plusOL x1 x2) := ((plus Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars zeroOL := (zero Bo)  
  | Bo vars (timesOL x1 x2) := ((times Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((BoundedJoinLattice A) → ((vector A n) → ((OpBoundedJoinLatticeTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars (plusOL2 x1 x2) := ((plus Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars zeroOL2 := (zero Bo)  
  | Bo vars (timesOL2 x1 x2) := ((times Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  def inductionB   (P : (BoundedJoinLatticeTerm → Type))  : ((∀ (x1 x2 : BoundedJoinLatticeTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 x2 : BoundedJoinLatticeTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : BoundedJoinLatticeTerm) , (P x))))) 
  | pplusl p0l ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l ptimesl x1) (inductionB pplusl p0l ptimesl x2))  
  | pplusl p0l ptimesl zeroL := p0l  
  | pplusl p0l ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl p0l ptimesl x1) (inductionB pplusl p0l ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClBoundedJoinLatticeTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBoundedJoinLatticeTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 x2 : (ClBoundedJoinLatticeTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClBoundedJoinLatticeTerm A)) , (P x)))))) 
  | psing ppluscl p0cl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl p0cl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl ptimescl x1) (inductionCl psing ppluscl p0cl ptimescl x2))  
  | psing ppluscl p0cl ptimescl zeroCl := p0cl  
  | psing ppluscl p0cl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl p0cl ptimescl x1) (inductionCl psing ppluscl p0cl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpBoundedJoinLatticeTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBoundedJoinLatticeTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 x2 : (OpBoundedJoinLatticeTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpBoundedJoinLatticeTerm n)) , (P x)))))) 
  | pv pplusol p0ol ptimesol (v x1) := (pv x1)  
  | pv pplusol p0ol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol ptimesol x1) (inductionOpB pv pplusol p0ol ptimesol x2))  
  | pv pplusol p0ol ptimesol zeroOL := p0ol  
  | pv pplusol p0ol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol p0ol ptimesol x1) (inductionOpB pv pplusol p0ol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpBoundedJoinLatticeTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBoundedJoinLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpBoundedJoinLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpBoundedJoinLatticeTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 x2))  
  def stageB  : (BoundedJoinLatticeTerm → (Staged BoundedJoinLatticeTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClBoundedJoinLatticeTerm A) → (Staged (ClBoundedJoinLatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpBoundedJoinLatticeTerm n) → (Staged (OpBoundedJoinLatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpBoundedJoinLatticeTerm2 n A) → (Staged (OpBoundedJoinLatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end BoundedJoinLattice