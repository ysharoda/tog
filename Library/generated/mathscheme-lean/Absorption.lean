import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Absorption   
  structure Absorption  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (leftAbsorp_times_plus : (∀ {x y : A} , (times x (plus x y)) = x))
       (leftAbsorp_plus_times : (∀ {x y : A} , (plus x (times x y)) = x)) 
  
  open Absorption
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftAbsorp_times_plusP : (∀ {xP yP : (Prod A A)} , (timesP xP (plusP xP yP)) = xP))
       (leftAbsorp_plus_timesP : (∀ {xP yP : (Prod A A)} , (plusP xP (timesP xP yP)) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ab1 : (Absorption A1)) (Ab2 : (Absorption A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ab1) x1 x2)) = ((times Ab2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ab1) x1 x2)) = ((plus Ab2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ab1 : (Absorption A1)) (Ab2 : (Absorption A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ab1) x1 x2) ((times Ab2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ab1) x1 x2) ((plus Ab2) y1 y2)))))) 
  
  inductive AbsorptionTerm   : Type  
     | timesL : (AbsorptionTerm → (AbsorptionTerm → AbsorptionTerm)) 
     | plusL : (AbsorptionTerm → (AbsorptionTerm → AbsorptionTerm))  
      open AbsorptionTerm 
  
  inductive ClAbsorptionTerm  (A : Type) : Type  
     | sing : (A → ClAbsorptionTerm) 
     | timesCl : (ClAbsorptionTerm → (ClAbsorptionTerm → ClAbsorptionTerm)) 
     | plusCl : (ClAbsorptionTerm → (ClAbsorptionTerm → ClAbsorptionTerm))  
      open ClAbsorptionTerm 
  
  inductive OpAbsorptionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAbsorptionTerm) 
     | timesOL : (OpAbsorptionTerm → (OpAbsorptionTerm → OpAbsorptionTerm)) 
     | plusOL : (OpAbsorptionTerm → (OpAbsorptionTerm → OpAbsorptionTerm))  
      open OpAbsorptionTerm 
  
  inductive OpAbsorptionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAbsorptionTerm2) 
     | sing2 : (A → OpAbsorptionTerm2) 
     | timesOL2 : (OpAbsorptionTerm2 → (OpAbsorptionTerm2 → OpAbsorptionTerm2)) 
     | plusOL2 : (OpAbsorptionTerm2 → (OpAbsorptionTerm2 → OpAbsorptionTerm2))  
      open OpAbsorptionTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAbsorptionTerm A) → (ClAbsorptionTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAbsorptionTerm n) → (OpAbsorptionTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAbsorptionTerm2 n A) → (OpAbsorptionTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Absorption A) → (AbsorptionTerm → A)) 
  | Ab (timesL x1 x2) := ((times Ab) (evalB Ab x1) (evalB Ab x2))  
  | Ab (plusL x1 x2) := ((plus Ab) (evalB Ab x1) (evalB Ab x2))  
  def evalCl   {A : Type}  : ((Absorption A) → ((ClAbsorptionTerm A) → A)) 
  | Ab (sing x1) := x1  
  | Ab (timesCl x1 x2) := ((times Ab) (evalCl Ab x1) (evalCl Ab x2))  
  | Ab (plusCl x1 x2) := ((plus Ab) (evalCl Ab x1) (evalCl Ab x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Absorption A) → ((vector A n) → ((OpAbsorptionTerm n) → A))) 
  | Ab vars (v x1) := (nth vars x1)  
  | Ab vars (timesOL x1 x2) := ((times Ab) (evalOpB Ab vars x1) (evalOpB Ab vars x2))  
  | Ab vars (plusOL x1 x2) := ((plus Ab) (evalOpB Ab vars x1) (evalOpB Ab vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Absorption A) → ((vector A n) → ((OpAbsorptionTerm2 n A) → A))) 
  | Ab vars (v2 x1) := (nth vars x1)  
  | Ab vars (sing2 x1) := x1  
  | Ab vars (timesOL2 x1 x2) := ((times Ab) (evalOp Ab vars x1) (evalOp Ab vars x2))  
  | Ab vars (plusOL2 x1 x2) := ((plus Ab) (evalOp Ab vars x1) (evalOp Ab vars x2))  
  def inductionB   (P : (AbsorptionTerm → Type))  : ((∀ (x1 x2 : AbsorptionTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : AbsorptionTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : AbsorptionTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClAbsorptionTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAbsorptionTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClAbsorptionTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClAbsorptionTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAbsorptionTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAbsorptionTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpAbsorptionTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpAbsorptionTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAbsorptionTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAbsorptionTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpAbsorptionTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpAbsorptionTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (AbsorptionTerm → (Staged AbsorptionTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAbsorptionTerm A) → (Staged (ClAbsorptionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAbsorptionTerm n) → (Staged (OpAbsorptionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAbsorptionTerm2 n A) → (Staged (OpAbsorptionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Absorption