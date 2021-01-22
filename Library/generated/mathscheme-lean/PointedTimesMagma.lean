import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedTimesMagma   
  structure PointedTimesMagma  (A : Type) : Type := 
       (times : (A → (A → A)))
       (e : A) 
  
  open PointedTimesMagma
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedTimesMagma A1)) (Po2 : (PointedTimesMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Po1) x1 x2)) = ((times Po2) (hom x1) (hom x2))))
       (pres_e : (hom (e Po1)) = (e Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedTimesMagma A1)) (Po2 : (PointedTimesMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Po1) x1 x2) ((times Po2) y1 y2))))))
       (interp_e : (interp (e Po1) (e Po2))) 
  
  inductive PointedTimesMagmaTerm   : Type  
     | timesL : (PointedTimesMagmaTerm → (PointedTimesMagmaTerm → PointedTimesMagmaTerm)) 
     | eL : PointedTimesMagmaTerm  
      open PointedTimesMagmaTerm 
  
  inductive ClPointedTimesMagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointedTimesMagmaTerm) 
     | timesCl : (ClPointedTimesMagmaTerm → (ClPointedTimesMagmaTerm → ClPointedTimesMagmaTerm)) 
     | eCl : ClPointedTimesMagmaTerm  
      open ClPointedTimesMagmaTerm 
  
  inductive OpPointedTimesMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedTimesMagmaTerm) 
     | timesOL : (OpPointedTimesMagmaTerm → (OpPointedTimesMagmaTerm → OpPointedTimesMagmaTerm)) 
     | eOL : OpPointedTimesMagmaTerm  
      open OpPointedTimesMagmaTerm 
  
  inductive OpPointedTimesMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedTimesMagmaTerm2) 
     | sing2 : (A → OpPointedTimesMagmaTerm2) 
     | timesOL2 : (OpPointedTimesMagmaTerm2 → (OpPointedTimesMagmaTerm2 → OpPointedTimesMagmaTerm2)) 
     | eOL2 : OpPointedTimesMagmaTerm2  
      open OpPointedTimesMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPointedTimesMagmaTerm A) → (ClPointedTimesMagmaTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPointedTimesMagmaTerm n) → (OpPointedTimesMagmaTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPointedTimesMagmaTerm2 n A) → (OpPointedTimesMagmaTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedTimesMagma A) → (PointedTimesMagmaTerm → A)) 
  | Po (timesL x1 x2) := ((times Po) (evalB Po x1) (evalB Po x2))  
  | Po eL := (e Po)  
  def evalCl   {A : Type}  : ((PointedTimesMagma A) → ((ClPointedTimesMagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po (timesCl x1 x2) := ((times Po) (evalCl Po x1) (evalCl Po x2))  
  | Po eCl := (e Po)  
  def evalOpB   {A : Type} {n : ℕ}  : ((PointedTimesMagma A) → ((vector A n) → ((OpPointedTimesMagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars (timesOL x1 x2) := ((times Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  | Po vars eOL := (e Po)  
  def evalOp   {A : Type} {n : ℕ}  : ((PointedTimesMagma A) → ((vector A n) → ((OpPointedTimesMagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars (timesOL2 x1 x2) := ((times Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  | Po vars eOL2 := (e Po)  
  def inductionB   {P : (PointedTimesMagmaTerm → Type)}  : ((∀ (x1 x2 : PointedTimesMagmaTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P eL) → (∀ (x : PointedTimesMagmaTerm) , (P x)))) 
  | ptimesl pel (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pel x1) (inductionB ptimesl pel x2))  
  | ptimesl pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClPointedTimesMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPointedTimesMagmaTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P eCl) → (∀ (x : (ClPointedTimesMagmaTerm A)) , (P x))))) 
  | psing ptimescl pecl (sing x1) := (psing x1)  
  | psing ptimescl pecl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl pecl x1) (inductionCl psing ptimescl pecl x2))  
  | psing ptimescl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpPointedTimesMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPointedTimesMagmaTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P eOL) → (∀ (x : (OpPointedTimesMagmaTerm n)) , (P x))))) 
  | pv ptimesol peol (v x1) := (pv x1)  
  | pv ptimesol peol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol peol x1) (inductionOpB pv ptimesol peol x2))  
  | pv ptimesol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPointedTimesMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPointedTimesMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpPointedTimesMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 peol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 peol2 x1) (inductionOp pv2 psing2 ptimesol2 peol2 x2))  
  | pv2 psing2 ptimesol2 peol2 eOL2 := peol2  
  def stageB  : (PointedTimesMagmaTerm → (Staged PointedTimesMagmaTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClPointedTimesMagmaTerm A) → (Staged (ClPointedTimesMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpPointedTimesMagmaTerm n) → (Staged (OpPointedTimesMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPointedTimesMagmaTerm2 n A) → (Staged (OpPointedTimesMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end PointedTimesMagma