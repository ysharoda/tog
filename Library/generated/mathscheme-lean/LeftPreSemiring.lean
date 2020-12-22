import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftPreSemiring   
  structure LeftPreSemiring  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z)))) 
  
  open LeftPreSemiring
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftPreSemiring A1)) (Le2 : (LeftPreSemiring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Le1) x1 x2)) = ((times Le2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Le1) x1 x2)) = ((plus Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftPreSemiring A1)) (Le2 : (LeftPreSemiring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Le1) x1 x2) ((times Le2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Le1) x1 x2) ((plus Le2) y1 y2)))))) 
  
  inductive LeftPreSemiringTerm   : Type  
     | timesL : (LeftPreSemiringTerm → (LeftPreSemiringTerm → LeftPreSemiringTerm)) 
     | plusL : (LeftPreSemiringTerm → (LeftPreSemiringTerm → LeftPreSemiringTerm))  
      open LeftPreSemiringTerm 
  
  inductive ClLeftPreSemiringTerm  (A : Type) : Type  
     | sing : (A → ClLeftPreSemiringTerm) 
     | timesCl : (ClLeftPreSemiringTerm → (ClLeftPreSemiringTerm → ClLeftPreSemiringTerm)) 
     | plusCl : (ClLeftPreSemiringTerm → (ClLeftPreSemiringTerm → ClLeftPreSemiringTerm))  
      open ClLeftPreSemiringTerm 
  
  inductive OpLeftPreSemiringTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftPreSemiringTerm) 
     | timesOL : (OpLeftPreSemiringTerm → (OpLeftPreSemiringTerm → OpLeftPreSemiringTerm)) 
     | plusOL : (OpLeftPreSemiringTerm → (OpLeftPreSemiringTerm → OpLeftPreSemiringTerm))  
      open OpLeftPreSemiringTerm 
  
  inductive OpLeftPreSemiringTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftPreSemiringTerm2) 
     | sing2 : (A → OpLeftPreSemiringTerm2) 
     | timesOL2 : (OpLeftPreSemiringTerm2 → (OpLeftPreSemiringTerm2 → OpLeftPreSemiringTerm2)) 
     | plusOL2 : (OpLeftPreSemiringTerm2 → (OpLeftPreSemiringTerm2 → OpLeftPreSemiringTerm2))  
      open OpLeftPreSemiringTerm2 
  
  def simplifyCl   (A : Type)  : ((ClLeftPreSemiringTerm A) → (ClLeftPreSemiringTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpLeftPreSemiringTerm n) → (OpLeftPreSemiringTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpLeftPreSemiringTerm2 n A) → (OpLeftPreSemiringTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftPreSemiring A) → (LeftPreSemiringTerm → A)) 
  | Le (timesL x1 x2) := ((times Le) (evalB Le x1) (evalB Le x2))  
  | Le (plusL x1 x2) := ((plus Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftPreSemiring A) → ((ClLeftPreSemiringTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (timesCl x1 x2) := ((times Le) (evalCl Le x1) (evalCl Le x2))  
  | Le (plusCl x1 x2) := ((plus Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((LeftPreSemiring A) → ((vector A n) → ((OpLeftPreSemiringTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (timesOL x1 x2) := ((times Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  | Le vars (plusOL x1 x2) := ((plus Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((LeftPreSemiring A) → ((vector A n) → ((OpLeftPreSemiringTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (timesOL2 x1 x2) := ((times Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  | Le vars (plusOL2 x1 x2) := ((plus Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   (P : (LeftPreSemiringTerm → Type))  : ((∀ (x1 x2 : LeftPreSemiringTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : LeftPreSemiringTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : LeftPreSemiringTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClLeftPreSemiringTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftPreSemiringTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClLeftPreSemiringTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClLeftPreSemiringTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpLeftPreSemiringTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftPreSemiringTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpLeftPreSemiringTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpLeftPreSemiringTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpLeftPreSemiringTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftPreSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpLeftPreSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpLeftPreSemiringTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (LeftPreSemiringTerm → (Staged LeftPreSemiringTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClLeftPreSemiringTerm A) → (Staged (ClLeftPreSemiringTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpLeftPreSemiringTerm n) → (Staged (OpLeftPreSemiringTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpLeftPreSemiringTerm2 n A) → (Staged (OpLeftPreSemiringTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftPreSemiring