import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section DistributiveLattice   
  structure DistributiveLattice  (A : Type) : Type := 
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
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z)))) 
  
  open DistributiveLattice
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP))
       (leftAbsorp_times_plusP : (∀ {xP yP : (Prod A A)} , (timesP xP (plusP xP yP)) = xP))
       (leftAbsorp_plus_timesP : (∀ {xP yP : (Prod A A)} , (plusP xP (timesP xP yP)) = xP))
       (leftModular_times_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (timesP xP yP) (timesP xP zP)) = (timesP xP (plusP yP (timesP xP zP)))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Di1 : (DistributiveLattice A1)) (Di2 : (DistributiveLattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Di1) x1 x2)) = ((times Di2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Di1) x1 x2)) = ((plus Di2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Di1 : (DistributiveLattice A1)) (Di2 : (DistributiveLattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Di1) x1 x2) ((times Di2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Di1) x1 x2) ((plus Di2) y1 y2)))))) 
  
  inductive DistributiveLatticeTerm   : Type  
     | timesL : (DistributiveLatticeTerm → (DistributiveLatticeTerm → DistributiveLatticeTerm)) 
     | plusL : (DistributiveLatticeTerm → (DistributiveLatticeTerm → DistributiveLatticeTerm))  
      open DistributiveLatticeTerm 
  
  inductive ClDistributiveLatticeTerm  (A : Type) : Type  
     | sing : (A → ClDistributiveLatticeTerm) 
     | timesCl : (ClDistributiveLatticeTerm → (ClDistributiveLatticeTerm → ClDistributiveLatticeTerm)) 
     | plusCl : (ClDistributiveLatticeTerm → (ClDistributiveLatticeTerm → ClDistributiveLatticeTerm))  
      open ClDistributiveLatticeTerm 
  
  inductive OpDistributiveLatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpDistributiveLatticeTerm) 
     | timesOL : (OpDistributiveLatticeTerm → (OpDistributiveLatticeTerm → OpDistributiveLatticeTerm)) 
     | plusOL : (OpDistributiveLatticeTerm → (OpDistributiveLatticeTerm → OpDistributiveLatticeTerm))  
      open OpDistributiveLatticeTerm 
  
  inductive OpDistributiveLatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpDistributiveLatticeTerm2) 
     | sing2 : (A → OpDistributiveLatticeTerm2) 
     | timesOL2 : (OpDistributiveLatticeTerm2 → (OpDistributiveLatticeTerm2 → OpDistributiveLatticeTerm2)) 
     | plusOL2 : (OpDistributiveLatticeTerm2 → (OpDistributiveLatticeTerm2 → OpDistributiveLatticeTerm2))  
      open OpDistributiveLatticeTerm2 
  
  def simplifyCl   (A : Type)  : ((ClDistributiveLatticeTerm A) → (ClDistributiveLatticeTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpDistributiveLatticeTerm n) → (OpDistributiveLatticeTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpDistributiveLatticeTerm2 n A) → (OpDistributiveLatticeTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((DistributiveLattice A) → (DistributiveLatticeTerm → A)) 
  | Di (timesL x1 x2) := ((times Di) (evalB Di x1) (evalB Di x2))  
  | Di (plusL x1 x2) := ((plus Di) (evalB Di x1) (evalB Di x2))  
  def evalCl   {A : Type}  : ((DistributiveLattice A) → ((ClDistributiveLatticeTerm A) → A)) 
  | Di (sing x1) := x1  
  | Di (timesCl x1 x2) := ((times Di) (evalCl Di x1) (evalCl Di x2))  
  | Di (plusCl x1 x2) := ((plus Di) (evalCl Di x1) (evalCl Di x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((DistributiveLattice A) → ((vector A n) → ((OpDistributiveLatticeTerm n) → A))) 
  | Di vars (v x1) := (nth vars x1)  
  | Di vars (timesOL x1 x2) := ((times Di) (evalOpB Di vars x1) (evalOpB Di vars x2))  
  | Di vars (plusOL x1 x2) := ((plus Di) (evalOpB Di vars x1) (evalOpB Di vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((DistributiveLattice A) → ((vector A n) → ((OpDistributiveLatticeTerm2 n A) → A))) 
  | Di vars (v2 x1) := (nth vars x1)  
  | Di vars (sing2 x1) := x1  
  | Di vars (timesOL2 x1 x2) := ((times Di) (evalOp Di vars x1) (evalOp Di vars x2))  
  | Di vars (plusOL2 x1 x2) := ((plus Di) (evalOp Di vars x1) (evalOp Di vars x2))  
  def inductionB   (P : (DistributiveLatticeTerm → Type))  : ((∀ (x1 x2 : DistributiveLatticeTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : DistributiveLatticeTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : DistributiveLatticeTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClDistributiveLatticeTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClDistributiveLatticeTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClDistributiveLatticeTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClDistributiveLatticeTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpDistributiveLatticeTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpDistributiveLatticeTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpDistributiveLatticeTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpDistributiveLatticeTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpDistributiveLatticeTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpDistributiveLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpDistributiveLatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpDistributiveLatticeTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (DistributiveLatticeTerm → (Staged DistributiveLatticeTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClDistributiveLatticeTerm A) → (Staged (ClDistributiveLatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpDistributiveLatticeTerm n) → (Staged (OpDistributiveLatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpDistributiveLatticeTerm2 n A) → (Staged (OpDistributiveLatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end DistributiveLattice