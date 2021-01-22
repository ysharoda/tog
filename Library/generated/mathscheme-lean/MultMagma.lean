import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultMagma   
  structure MultMagma  (A : Type) : Type := 
       (times : (A → (A → A))) 
  
  open MultMagma
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultMagma A1)) (Mu2 : (MultMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultMagma A1)) (Mu2 : (MultMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2)))))) 
  
  inductive MultMagmaTerm   : Type  
     | timesL : (MultMagmaTerm → (MultMagmaTerm → MultMagmaTerm))  
      open MultMagmaTerm 
  
  inductive ClMultMagmaTerm  (A : Type) : Type  
     | sing : (A → ClMultMagmaTerm) 
     | timesCl : (ClMultMagmaTerm → (ClMultMagmaTerm → ClMultMagmaTerm))  
      open ClMultMagmaTerm 
  
  inductive OpMultMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultMagmaTerm) 
     | timesOL : (OpMultMagmaTerm → (OpMultMagmaTerm → OpMultMagmaTerm))  
      open OpMultMagmaTerm 
  
  inductive OpMultMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultMagmaTerm2) 
     | sing2 : (A → OpMultMagmaTerm2) 
     | timesOL2 : (OpMultMagmaTerm2 → (OpMultMagmaTerm2 → OpMultMagmaTerm2))  
      open OpMultMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMultMagmaTerm A) → (ClMultMagmaTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMultMagmaTerm n) → (OpMultMagmaTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMultMagmaTerm2 n A) → (OpMultMagmaTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultMagma A) → (MultMagmaTerm → A)) 
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  def evalCl   {A : Type}  : ((MultMagma A) → ((ClMultMagmaTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((MultMagma A) → ((vector A n) → ((OpMultMagmaTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((MultMagma A) → ((vector A n) → ((OpMultMagmaTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  def inductionB   {P : (MultMagmaTerm → Type)}  : ((∀ (x1 x2 : MultMagmaTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : MultMagmaTerm) , (P x))) 
  | ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl x1) (inductionB ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClMultMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMultMagmaTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClMultMagmaTerm A)) , (P x)))) 
  | psing ptimescl (sing x1) := (psing x1)  
  | psing ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl x1) (inductionCl psing ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMultMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMultMagmaTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpMultMagmaTerm n)) , (P x)))) 
  | pv ptimesol (v x1) := (pv x1)  
  | pv ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol x1) (inductionOpB pv ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMultMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMultMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpMultMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 x1) (inductionOp pv2 psing2 ptimesol2 x2))  
  def stageB  : (MultMagmaTerm → (Staged MultMagmaTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMultMagmaTerm A) → (Staged (ClMultMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMultMagmaTerm n) → (Staged (OpMultMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMultMagmaTerm2 n A) → (Staged (OpMultMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MultMagma