import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section OrDeMorgran   
  structure OrDeMorgran  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (prim : (A → A))
       (orDeMorgan_plus_times_prim : (∀ {x y z : A} , (prim (plus x y)) = (times (prim x) (prim y)))) 
  
  open OrDeMorgran
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (orDeMorgan_plus_times_primP : (∀ {xP yP zP : (Prod A A)} , (primP (plusP xP yP)) = (timesP (primP xP) (primP yP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Or1 : (OrDeMorgran A1)) (Or2 : (OrDeMorgran A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Or1) x1 x2)) = ((times Or2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Or1) x1 x2)) = ((plus Or2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Or1) x1)) = ((prim Or2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Or1 : (OrDeMorgran A1)) (Or2 : (OrDeMorgran A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Or1) x1 x2) ((times Or2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Or1) x1 x2) ((plus Or2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Or1) x1) ((prim Or2) y1))))) 
  
  inductive OrDeMorgranTerm   : Type  
     | timesL : (OrDeMorgranTerm → (OrDeMorgranTerm → OrDeMorgranTerm)) 
     | plusL : (OrDeMorgranTerm → (OrDeMorgranTerm → OrDeMorgranTerm)) 
     | primL : (OrDeMorgranTerm → OrDeMorgranTerm)  
      open OrDeMorgranTerm 
  
  inductive ClOrDeMorgranTerm  (A : Type) : Type  
     | sing : (A → ClOrDeMorgranTerm) 
     | timesCl : (ClOrDeMorgranTerm → (ClOrDeMorgranTerm → ClOrDeMorgranTerm)) 
     | plusCl : (ClOrDeMorgranTerm → (ClOrDeMorgranTerm → ClOrDeMorgranTerm)) 
     | primCl : (ClOrDeMorgranTerm → ClOrDeMorgranTerm)  
      open ClOrDeMorgranTerm 
  
  inductive OpOrDeMorgranTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpOrDeMorgranTerm) 
     | timesOL : (OpOrDeMorgranTerm → (OpOrDeMorgranTerm → OpOrDeMorgranTerm)) 
     | plusOL : (OpOrDeMorgranTerm → (OpOrDeMorgranTerm → OpOrDeMorgranTerm)) 
     | primOL : (OpOrDeMorgranTerm → OpOrDeMorgranTerm)  
      open OpOrDeMorgranTerm 
  
  inductive OpOrDeMorgranTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpOrDeMorgranTerm2) 
     | sing2 : (A → OpOrDeMorgranTerm2) 
     | timesOL2 : (OpOrDeMorgranTerm2 → (OpOrDeMorgranTerm2 → OpOrDeMorgranTerm2)) 
     | plusOL2 : (OpOrDeMorgranTerm2 → (OpOrDeMorgranTerm2 → OpOrDeMorgranTerm2)) 
     | primOL2 : (OpOrDeMorgranTerm2 → OpOrDeMorgranTerm2)  
      open OpOrDeMorgranTerm2 
  
  def simplifyCl   {A : Type}  : ((ClOrDeMorgranTerm A) → (ClOrDeMorgranTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpOrDeMorgranTerm n) → (OpOrDeMorgranTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpOrDeMorgranTerm2 n A) → (OpOrDeMorgranTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((OrDeMorgran A) → (OrDeMorgranTerm → A)) 
  | Or (timesL x1 x2) := ((times Or) (evalB Or x1) (evalB Or x2))  
  | Or (plusL x1 x2) := ((plus Or) (evalB Or x1) (evalB Or x2))  
  | Or (primL x1) := ((prim Or) (evalB Or x1))  
  def evalCl   {A : Type}  : ((OrDeMorgran A) → ((ClOrDeMorgranTerm A) → A)) 
  | Or (sing x1) := x1  
  | Or (timesCl x1 x2) := ((times Or) (evalCl Or x1) (evalCl Or x2))  
  | Or (plusCl x1 x2) := ((plus Or) (evalCl Or x1) (evalCl Or x2))  
  | Or (primCl x1) := ((prim Or) (evalCl Or x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((OrDeMorgran A) → ((vector A n) → ((OpOrDeMorgranTerm n) → A))) 
  | Or vars (v x1) := (nth vars x1)  
  | Or vars (timesOL x1 x2) := ((times Or) (evalOpB Or vars x1) (evalOpB Or vars x2))  
  | Or vars (plusOL x1 x2) := ((plus Or) (evalOpB Or vars x1) (evalOpB Or vars x2))  
  | Or vars (primOL x1) := ((prim Or) (evalOpB Or vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((OrDeMorgran A) → ((vector A n) → ((OpOrDeMorgranTerm2 n A) → A))) 
  | Or vars (v2 x1) := (nth vars x1)  
  | Or vars (sing2 x1) := x1  
  | Or vars (timesOL2 x1 x2) := ((times Or) (evalOp Or vars x1) (evalOp Or vars x2))  
  | Or vars (plusOL2 x1 x2) := ((plus Or) (evalOp Or vars x1) (evalOp Or vars x2))  
  | Or vars (primOL2 x1) := ((prim Or) (evalOp Or vars x1))  
  def inductionB   {P : (OrDeMorgranTerm → Type)}  : ((∀ (x1 x2 : OrDeMorgranTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : OrDeMorgranTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : OrDeMorgranTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : OrDeMorgranTerm) , (P x))))) 
  | ptimesl pplusl ppriml (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (primL x1) := (ppriml _ (inductionB ptimesl pplusl ppriml x1))  
  def inductionCl   {A : Type} {P : ((ClOrDeMorgranTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClOrDeMorgranTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClOrDeMorgranTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClOrDeMorgranTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClOrDeMorgranTerm A)) , (P x)))))) 
  | psing ptimescl ppluscl pprimcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl pprimcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl ppluscl pprimcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpOrDeMorgranTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpOrDeMorgranTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpOrDeMorgranTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpOrDeMorgranTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpOrDeMorgranTerm n)) , (P x)))))) 
  | pv ptimesol pplusol pprimol (v x1) := (pv x1)  
  | pv ptimesol pplusol pprimol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pplusol pprimol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpOrDeMorgranTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpOrDeMorgranTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpOrDeMorgranTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpOrDeMorgranTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpOrDeMorgranTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1))  
  def stageB  : (OrDeMorgranTerm → (Staged OrDeMorgranTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClOrDeMorgranTerm A) → (Staged (ClOrDeMorgranTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpOrDeMorgranTerm n) → (Staged (OpOrDeMorgranTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpOrDeMorgranTerm2 n A) → (Staged (OpOrDeMorgranTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end OrDeMorgran