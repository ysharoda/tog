import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section NonDistributiveAddPreSemiring   
  structure NonDistributiveAddPreSemiring  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (times : (A → (A → A))) 
  
  open NonDistributiveAddPreSemiring
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (No1 : (NonDistributiveAddPreSemiring A1)) (No2 : (NonDistributiveAddPreSemiring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus No1) x1 x2)) = ((plus No2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times No1) x1 x2)) = ((times No2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (No1 : (NonDistributiveAddPreSemiring A1)) (No2 : (NonDistributiveAddPreSemiring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus No1) x1 x2) ((plus No2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times No1) x1 x2) ((times No2) y1 y2)))))) 
  
  inductive NonDistributiveAddPreSemiringTerm   : Type  
     | plusL : (NonDistributiveAddPreSemiringTerm → (NonDistributiveAddPreSemiringTerm → NonDistributiveAddPreSemiringTerm)) 
     | timesL : (NonDistributiveAddPreSemiringTerm → (NonDistributiveAddPreSemiringTerm → NonDistributiveAddPreSemiringTerm))  
      open NonDistributiveAddPreSemiringTerm 
  
  inductive ClNonDistributiveAddPreSemiringTerm  (A : Type) : Type  
     | sing : (A → ClNonDistributiveAddPreSemiringTerm) 
     | plusCl : (ClNonDistributiveAddPreSemiringTerm → (ClNonDistributiveAddPreSemiringTerm → ClNonDistributiveAddPreSemiringTerm)) 
     | timesCl : (ClNonDistributiveAddPreSemiringTerm → (ClNonDistributiveAddPreSemiringTerm → ClNonDistributiveAddPreSemiringTerm))  
      open ClNonDistributiveAddPreSemiringTerm 
  
  inductive OpNonDistributiveAddPreSemiringTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpNonDistributiveAddPreSemiringTerm) 
     | plusOL : (OpNonDistributiveAddPreSemiringTerm → (OpNonDistributiveAddPreSemiringTerm → OpNonDistributiveAddPreSemiringTerm)) 
     | timesOL : (OpNonDistributiveAddPreSemiringTerm → (OpNonDistributiveAddPreSemiringTerm → OpNonDistributiveAddPreSemiringTerm))  
      open OpNonDistributiveAddPreSemiringTerm 
  
  inductive OpNonDistributiveAddPreSemiringTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpNonDistributiveAddPreSemiringTerm2) 
     | sing2 : (A → OpNonDistributiveAddPreSemiringTerm2) 
     | plusOL2 : (OpNonDistributiveAddPreSemiringTerm2 → (OpNonDistributiveAddPreSemiringTerm2 → OpNonDistributiveAddPreSemiringTerm2)) 
     | timesOL2 : (OpNonDistributiveAddPreSemiringTerm2 → (OpNonDistributiveAddPreSemiringTerm2 → OpNonDistributiveAddPreSemiringTerm2))  
      open OpNonDistributiveAddPreSemiringTerm2 
  
  def simplifyCl   (A : Type)  : ((ClNonDistributiveAddPreSemiringTerm A) → (ClNonDistributiveAddPreSemiringTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpNonDistributiveAddPreSemiringTerm n) → (OpNonDistributiveAddPreSemiringTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpNonDistributiveAddPreSemiringTerm2 n A) → (OpNonDistributiveAddPreSemiringTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((NonDistributiveAddPreSemiring A) → (NonDistributiveAddPreSemiringTerm → A)) 
  | No (plusL x1 x2) := ((plus No) (evalB No x1) (evalB No x2))  
  | No (timesL x1 x2) := ((times No) (evalB No x1) (evalB No x2))  
  def evalCl   {A : Type}  : ((NonDistributiveAddPreSemiring A) → ((ClNonDistributiveAddPreSemiringTerm A) → A)) 
  | No (sing x1) := x1  
  | No (plusCl x1 x2) := ((plus No) (evalCl No x1) (evalCl No x2))  
  | No (timesCl x1 x2) := ((times No) (evalCl No x1) (evalCl No x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((NonDistributiveAddPreSemiring A) → ((vector A n) → ((OpNonDistributiveAddPreSemiringTerm n) → A))) 
  | No vars (v x1) := (nth vars x1)  
  | No vars (plusOL x1 x2) := ((plus No) (evalOpB No vars x1) (evalOpB No vars x2))  
  | No vars (timesOL x1 x2) := ((times No) (evalOpB No vars x1) (evalOpB No vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((NonDistributiveAddPreSemiring A) → ((vector A n) → ((OpNonDistributiveAddPreSemiringTerm2 n A) → A))) 
  | No vars (v2 x1) := (nth vars x1)  
  | No vars (sing2 x1) := x1  
  | No vars (plusOL2 x1 x2) := ((plus No) (evalOp No vars x1) (evalOp No vars x2))  
  | No vars (timesOL2 x1 x2) := ((times No) (evalOp No vars x1) (evalOp No vars x2))  
  def inductionB   (P : (NonDistributiveAddPreSemiringTerm → Type))  : ((∀ (x1 x2 : NonDistributiveAddPreSemiringTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : NonDistributiveAddPreSemiringTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : NonDistributiveAddPreSemiringTerm) , (P x)))) 
  | pplusl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl ptimesl x1) (inductionB pplusl ptimesl x2))  
  | pplusl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl ptimesl x1) (inductionB pplusl ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClNonDistributiveAddPreSemiringTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClNonDistributiveAddPreSemiringTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClNonDistributiveAddPreSemiringTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClNonDistributiveAddPreSemiringTerm A)) , (P x))))) 
  | psing ppluscl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl ptimescl x1) (inductionCl psing ppluscl ptimescl x2))  
  | psing ppluscl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl ptimescl x1) (inductionCl psing ppluscl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpNonDistributiveAddPreSemiringTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpNonDistributiveAddPreSemiringTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpNonDistributiveAddPreSemiringTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpNonDistributiveAddPreSemiringTerm n)) , (P x))))) 
  | pv pplusol ptimesol (v x1) := (pv x1)  
  | pv pplusol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol ptimesol x1) (inductionOpB pv pplusol ptimesol x2))  
  | pv pplusol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol ptimesol x1) (inductionOpB pv pplusol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpNonDistributiveAddPreSemiringTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpNonDistributiveAddPreSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpNonDistributiveAddPreSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpNonDistributiveAddPreSemiringTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 x2))  
  def stageB  : (NonDistributiveAddPreSemiringTerm → (Staged NonDistributiveAddPreSemiringTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClNonDistributiveAddPreSemiringTerm A) → (Staged (ClNonDistributiveAddPreSemiringTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpNonDistributiveAddPreSemiringTerm n) → (Staged (OpNonDistributiveAddPreSemiringTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpNonDistributiveAddPreSemiringTerm2 n A) → (Staged (OpNonDistributiveAddPreSemiringTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end NonDistributiveAddPreSemiring