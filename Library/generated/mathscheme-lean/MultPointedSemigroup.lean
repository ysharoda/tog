import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultPointedSemigroup   
  structure MultPointedSemigroup  (A : Type) : Type := 
       (one : A)
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z)))) 
  
  open MultPointedSemigroup
  structure Sig  (AS : Type) : Type := 
       (oneS : AS)
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultPointedSemigroup A1)) (Mu2 : (MultPointedSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one Mu1)) = (one Mu2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultPointedSemigroup A1)) (Mu2 : (MultPointedSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one Mu1) (one Mu2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2)))))) 
  
  inductive MultPointedSemigroupTerm   : Type  
     | oneL : MultPointedSemigroupTerm 
     | timesL : (MultPointedSemigroupTerm → (MultPointedSemigroupTerm → MultPointedSemigroupTerm))  
      open MultPointedSemigroupTerm 
  
  inductive ClMultPointedSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClMultPointedSemigroupTerm) 
     | oneCl : ClMultPointedSemigroupTerm 
     | timesCl : (ClMultPointedSemigroupTerm → (ClMultPointedSemigroupTerm → ClMultPointedSemigroupTerm))  
      open ClMultPointedSemigroupTerm 
  
  inductive OpMultPointedSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultPointedSemigroupTerm) 
     | oneOL : OpMultPointedSemigroupTerm 
     | timesOL : (OpMultPointedSemigroupTerm → (OpMultPointedSemigroupTerm → OpMultPointedSemigroupTerm))  
      open OpMultPointedSemigroupTerm 
  
  inductive OpMultPointedSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultPointedSemigroupTerm2) 
     | sing2 : (A → OpMultPointedSemigroupTerm2) 
     | oneOL2 : OpMultPointedSemigroupTerm2 
     | timesOL2 : (OpMultPointedSemigroupTerm2 → (OpMultPointedSemigroupTerm2 → OpMultPointedSemigroupTerm2))  
      open OpMultPointedSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMultPointedSemigroupTerm A) → (ClMultPointedSemigroupTerm A)) 
  | oneCl := oneCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMultPointedSemigroupTerm n) → (OpMultPointedSemigroupTerm n)) 
  | oneOL := oneOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMultPointedSemigroupTerm2 n A) → (OpMultPointedSemigroupTerm2 n A)) 
  | oneOL2 := oneOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultPointedSemigroup A) → (MultPointedSemigroupTerm → A)) 
  | Mu oneL := (one Mu)  
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  def evalCl   {A : Type}  : ((MultPointedSemigroup A) → ((ClMultPointedSemigroupTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu oneCl := (one Mu)  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MultPointedSemigroup A) → ((vector A n) → ((OpMultPointedSemigroupTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars oneOL := (one Mu)  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((MultPointedSemigroup A) → ((vector A n) → ((OpMultPointedSemigroupTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars oneOL2 := (one Mu)  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  def inductionB   (P : (MultPointedSemigroupTerm → Type))  : ((P oneL) → ((∀ (x1 x2 : MultPointedSemigroupTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : MultPointedSemigroupTerm) , (P x)))) 
  | p1l ptimesl oneL := p1l  
  | p1l ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p1l ptimesl x1) (inductionB p1l ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClMultPointedSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → ((∀ (x1 x2 : (ClMultPointedSemigroupTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClMultPointedSemigroupTerm A)) , (P x))))) 
  | psing p1cl ptimescl (sing x1) := (psing x1)  
  | psing p1cl ptimescl oneCl := p1cl  
  | psing p1cl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p1cl ptimescl x1) (inductionCl psing p1cl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpMultPointedSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → ((∀ (x1 x2 : (OpMultPointedSemigroupTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpMultPointedSemigroupTerm n)) , (P x))))) 
  | pv p1ol ptimesol (v x1) := (pv x1)  
  | pv p1ol ptimesol oneOL := p1ol  
  | pv p1ol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p1ol ptimesol x1) (inductionOpB pv p1ol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMultPointedSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → ((∀ (x1 x2 : (OpMultPointedSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpMultPointedSemigroupTerm2 n A)) , (P x)))))) 
  | pv2 psing2 p1ol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 ptimesol2 oneOL2 := p1ol2  
  | pv2 psing2 p1ol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p1ol2 ptimesol2 x1) (inductionOp pv2 psing2 p1ol2 ptimesol2 x2))  
  def stageB  : (MultPointedSemigroupTerm → (Staged MultPointedSemigroupTerm))
  | oneL := (Now oneL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClMultPointedSemigroupTerm A) → (Staged (ClMultPointedSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpMultPointedSemigroupTerm n) → (Staged (OpMultPointedSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMultPointedSemigroupTerm2 n A) → (Staged (OpMultPointedSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MultPointedSemigroup