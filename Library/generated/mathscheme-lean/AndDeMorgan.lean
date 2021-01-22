import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AndDeMorgan   
  structure AndDeMorgan  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (prim : (A → A))
       (andDeMorgan_times_plus_prim : (∀ {x y z : A} , (prim (times x y)) = (plus (prim x) (prim y)))) 
  
  open AndDeMorgan
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (andDeMorgan_times_plus_primP : (∀ {xP yP zP : (Prod A A)} , (primP (timesP xP yP)) = (plusP (primP xP) (primP yP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (An1 : (AndDeMorgan A1)) (An2 : (AndDeMorgan A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times An1) x1 x2)) = ((times An2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus An1) x1 x2)) = ((plus An2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim An1) x1)) = ((prim An2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (An1 : (AndDeMorgan A1)) (An2 : (AndDeMorgan A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times An1) x1 x2) ((times An2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus An1) x1 x2) ((plus An2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim An1) x1) ((prim An2) y1))))) 
  
  inductive AndDeMorganTerm   : Type  
     | timesL : (AndDeMorganTerm → (AndDeMorganTerm → AndDeMorganTerm)) 
     | plusL : (AndDeMorganTerm → (AndDeMorganTerm → AndDeMorganTerm)) 
     | primL : (AndDeMorganTerm → AndDeMorganTerm)  
      open AndDeMorganTerm 
  
  inductive ClAndDeMorganTerm  (A : Type) : Type  
     | sing : (A → ClAndDeMorganTerm) 
     | timesCl : (ClAndDeMorganTerm → (ClAndDeMorganTerm → ClAndDeMorganTerm)) 
     | plusCl : (ClAndDeMorganTerm → (ClAndDeMorganTerm → ClAndDeMorganTerm)) 
     | primCl : (ClAndDeMorganTerm → ClAndDeMorganTerm)  
      open ClAndDeMorganTerm 
  
  inductive OpAndDeMorganTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAndDeMorganTerm) 
     | timesOL : (OpAndDeMorganTerm → (OpAndDeMorganTerm → OpAndDeMorganTerm)) 
     | plusOL : (OpAndDeMorganTerm → (OpAndDeMorganTerm → OpAndDeMorganTerm)) 
     | primOL : (OpAndDeMorganTerm → OpAndDeMorganTerm)  
      open OpAndDeMorganTerm 
  
  inductive OpAndDeMorganTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAndDeMorganTerm2) 
     | sing2 : (A → OpAndDeMorganTerm2) 
     | timesOL2 : (OpAndDeMorganTerm2 → (OpAndDeMorganTerm2 → OpAndDeMorganTerm2)) 
     | plusOL2 : (OpAndDeMorganTerm2 → (OpAndDeMorganTerm2 → OpAndDeMorganTerm2)) 
     | primOL2 : (OpAndDeMorganTerm2 → OpAndDeMorganTerm2)  
      open OpAndDeMorganTerm2 
  
  def simplifyCl   {A : Type}  : ((ClAndDeMorganTerm A) → (ClAndDeMorganTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpAndDeMorganTerm n) → (OpAndDeMorganTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpAndDeMorganTerm2 n A) → (OpAndDeMorganTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AndDeMorgan A) → (AndDeMorganTerm → A)) 
  | An (timesL x1 x2) := ((times An) (evalB An x1) (evalB An x2))  
  | An (plusL x1 x2) := ((plus An) (evalB An x1) (evalB An x2))  
  | An (primL x1) := ((prim An) (evalB An x1))  
  def evalCl   {A : Type}  : ((AndDeMorgan A) → ((ClAndDeMorganTerm A) → A)) 
  | An (sing x1) := x1  
  | An (timesCl x1 x2) := ((times An) (evalCl An x1) (evalCl An x2))  
  | An (plusCl x1 x2) := ((plus An) (evalCl An x1) (evalCl An x2))  
  | An (primCl x1) := ((prim An) (evalCl An x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((AndDeMorgan A) → ((vector A n) → ((OpAndDeMorganTerm n) → A))) 
  | An vars (v x1) := (nth vars x1)  
  | An vars (timesOL x1 x2) := ((times An) (evalOpB An vars x1) (evalOpB An vars x2))  
  | An vars (plusOL x1 x2) := ((plus An) (evalOpB An vars x1) (evalOpB An vars x2))  
  | An vars (primOL x1) := ((prim An) (evalOpB An vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((AndDeMorgan A) → ((vector A n) → ((OpAndDeMorganTerm2 n A) → A))) 
  | An vars (v2 x1) := (nth vars x1)  
  | An vars (sing2 x1) := x1  
  | An vars (timesOL2 x1 x2) := ((times An) (evalOp An vars x1) (evalOp An vars x2))  
  | An vars (plusOL2 x1 x2) := ((plus An) (evalOp An vars x1) (evalOp An vars x2))  
  | An vars (primOL2 x1) := ((prim An) (evalOp An vars x1))  
  def inductionB   {P : (AndDeMorganTerm → Type)}  : ((∀ (x1 x2 : AndDeMorganTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : AndDeMorganTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : AndDeMorganTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : AndDeMorganTerm) , (P x))))) 
  | ptimesl pplusl ppriml (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl ppriml x1) (inductionB ptimesl pplusl ppriml x2))  
  | ptimesl pplusl ppriml (primL x1) := (ppriml _ (inductionB ptimesl pplusl ppriml x1))  
  def inductionCl   {A : Type} {P : ((ClAndDeMorganTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAndDeMorganTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClAndDeMorganTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClAndDeMorganTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClAndDeMorganTerm A)) , (P x)))))) 
  | psing ptimescl ppluscl pprimcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl pprimcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl pprimcl x1) (inductionCl psing ptimescl ppluscl pprimcl x2))  
  | psing ptimescl ppluscl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl ppluscl pprimcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpAndDeMorganTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAndDeMorganTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpAndDeMorganTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpAndDeMorganTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpAndDeMorganTerm n)) , (P x)))))) 
  | pv ptimesol pplusol pprimol (v x1) := (pv x1)  
  | pv ptimesol pplusol pprimol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol pprimol x1) (inductionOpB pv ptimesol pplusol pprimol x2))  
  | pv ptimesol pplusol pprimol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pplusol pprimol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpAndDeMorganTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAndDeMorganTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpAndDeMorganTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpAndDeMorganTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpAndDeMorganTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 pprimol2 x1))  
  def stageB  : (AndDeMorganTerm → (Staged AndDeMorganTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClAndDeMorganTerm A) → (Staged (ClAndDeMorganTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpAndDeMorganTerm n) → (Staged (OpAndDeMorganTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpAndDeMorganTerm2 n A) → (Staged (OpAndDeMorganTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end AndDeMorgan