import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultSemigroup   
  structure MultSemigroup  (A : Type) : Type := 
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z)))) 
  
  open MultSemigroup
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultSemigroup A1)) (Mu2 : (MultSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultSemigroup A1)) (Mu2 : (MultSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2)))))) 
  
  inductive MultSemigroupTerm   : Type  
     | timesL : (MultSemigroupTerm → (MultSemigroupTerm → MultSemigroupTerm))  
      open MultSemigroupTerm 
  
  inductive ClMultSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClMultSemigroupTerm) 
     | timesCl : (ClMultSemigroupTerm → (ClMultSemigroupTerm → ClMultSemigroupTerm))  
      open ClMultSemigroupTerm 
  
  inductive OpMultSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultSemigroupTerm) 
     | timesOL : (OpMultSemigroupTerm → (OpMultSemigroupTerm → OpMultSemigroupTerm))  
      open OpMultSemigroupTerm 
  
  inductive OpMultSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultSemigroupTerm2) 
     | sing2 : (A → OpMultSemigroupTerm2) 
     | timesOL2 : (OpMultSemigroupTerm2 → (OpMultSemigroupTerm2 → OpMultSemigroupTerm2))  
      open OpMultSemigroupTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMultSemigroupTerm A) → (ClMultSemigroupTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMultSemigroupTerm n) → (OpMultSemigroupTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMultSemigroupTerm2 n A) → (OpMultSemigroupTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultSemigroup A) → (MultSemigroupTerm → A)) 
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  def evalCl   {A : Type}  : ((MultSemigroup A) → ((ClMultSemigroupTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((MultSemigroup A) → ((vector A n) → ((OpMultSemigroupTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((MultSemigroup A) → ((vector A n) → ((OpMultSemigroupTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  def inductionB   {P : (MultSemigroupTerm → Type)}  : ((∀ (x1 x2 : MultSemigroupTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : MultSemigroupTerm) , (P x))) 
  | ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl x1) (inductionB ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClMultSemigroupTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMultSemigroupTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClMultSemigroupTerm A)) , (P x)))) 
  | psing ptimescl (sing x1) := (psing x1)  
  | psing ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl x1) (inductionCl psing ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMultSemigroupTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMultSemigroupTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpMultSemigroupTerm n)) , (P x)))) 
  | pv ptimesol (v x1) := (pv x1)  
  | pv ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol x1) (inductionOpB pv ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMultSemigroupTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMultSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpMultSemigroupTerm2 n A)) , (P x))))) 
  | pv2 psing2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 x1) (inductionOp pv2 psing2 ptimesol2 x2))  
  def stageB  : (MultSemigroupTerm → (Staged MultSemigroupTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMultSemigroupTerm A) → (Staged (ClMultSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMultSemigroupTerm n) → (Staged (OpMultSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMultSemigroupTerm2 n A) → (Staged (OpMultSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MultSemigroup