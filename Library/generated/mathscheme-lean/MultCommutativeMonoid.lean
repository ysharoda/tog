import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultCommutativeMonoid   
  structure MultCommutativeMonoid  (A : Type) : Type := 
       (times : (A → (A → A)))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x))) 
  
  open MultCommutativeMonoid
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultCommutativeMonoid A1)) (Mu2 : (MultCommutativeMonoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2))))
       (pres_one : (hom (one Mu1)) = (one Mu2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultCommutativeMonoid A1)) (Mu2 : (MultCommutativeMonoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2))))))
       (interp_one : (interp (one Mu1) (one Mu2))) 
  
  inductive MultCommutativeMonoidTerm   : Type  
     | timesL : (MultCommutativeMonoidTerm → (MultCommutativeMonoidTerm → MultCommutativeMonoidTerm)) 
     | oneL : MultCommutativeMonoidTerm  
      open MultCommutativeMonoidTerm 
  
  inductive ClMultCommutativeMonoidTerm  (A : Type) : Type  
     | sing : (A → ClMultCommutativeMonoidTerm) 
     | timesCl : (ClMultCommutativeMonoidTerm → (ClMultCommutativeMonoidTerm → ClMultCommutativeMonoidTerm)) 
     | oneCl : ClMultCommutativeMonoidTerm  
      open ClMultCommutativeMonoidTerm 
  
  inductive OpMultCommutativeMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultCommutativeMonoidTerm) 
     | timesOL : (OpMultCommutativeMonoidTerm → (OpMultCommutativeMonoidTerm → OpMultCommutativeMonoidTerm)) 
     | oneOL : OpMultCommutativeMonoidTerm  
      open OpMultCommutativeMonoidTerm 
  
  inductive OpMultCommutativeMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultCommutativeMonoidTerm2) 
     | sing2 : (A → OpMultCommutativeMonoidTerm2) 
     | timesOL2 : (OpMultCommutativeMonoidTerm2 → (OpMultCommutativeMonoidTerm2 → OpMultCommutativeMonoidTerm2)) 
     | oneOL2 : OpMultCommutativeMonoidTerm2  
      open OpMultCommutativeMonoidTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMultCommutativeMonoidTerm A) → (ClMultCommutativeMonoidTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMultCommutativeMonoidTerm n) → (OpMultCommutativeMonoidTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMultCommutativeMonoidTerm2 n A) → (OpMultCommutativeMonoidTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultCommutativeMonoid A) → (MultCommutativeMonoidTerm → A)) 
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  | Mu oneL := (one Mu)  
  def evalCl   {A : Type}  : ((MultCommutativeMonoid A) → ((ClMultCommutativeMonoidTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  | Mu oneCl := (one Mu)  
  def evalOpB   {A : Type} {n : ℕ}  : ((MultCommutativeMonoid A) → ((vector A n) → ((OpMultCommutativeMonoidTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  | Mu vars oneOL := (one Mu)  
  def evalOp   {A : Type} {n : ℕ}  : ((MultCommutativeMonoid A) → ((vector A n) → ((OpMultCommutativeMonoidTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  | Mu vars oneOL2 := (one Mu)  
  def inductionB   {P : (MultCommutativeMonoidTerm → Type)}  : ((∀ (x1 x2 : MultCommutativeMonoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → (∀ (x : MultCommutativeMonoidTerm) , (P x)))) 
  | ptimesl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l x1) (inductionB ptimesl p1l x2))  
  | ptimesl p1l oneL := p1l  
  def inductionCl   {A : Type} {P : ((ClMultCommutativeMonoidTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMultCommutativeMonoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → (∀ (x : (ClMultCommutativeMonoidTerm A)) , (P x))))) 
  | psing ptimescl p1cl (sing x1) := (psing x1)  
  | psing ptimescl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl x1) (inductionCl psing ptimescl p1cl x2))  
  | psing ptimescl p1cl oneCl := p1cl  
  def inductionOpB   {n : ℕ} {P : ((OpMultCommutativeMonoidTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMultCommutativeMonoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → (∀ (x : (OpMultCommutativeMonoidTerm n)) , (P x))))) 
  | pv ptimesol p1ol (v x1) := (pv x1)  
  | pv ptimesol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol x1) (inductionOpB pv ptimesol p1ol x2))  
  | pv ptimesol p1ol oneOL := p1ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMultCommutativeMonoidTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMultCommutativeMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → (∀ (x : (OpMultCommutativeMonoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (MultCommutativeMonoidTerm → (Staged MultCommutativeMonoidTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  def stageCl   {A : Type}  : ((ClMultCommutativeMonoidTerm A) → (Staged (ClMultCommutativeMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  def stageOpB   {n : ℕ}  : ((OpMultCommutativeMonoidTerm n) → (Staged (OpMultCommutativeMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMultCommutativeMonoidTerm2 n A) → (Staged (OpMultCommutativeMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A)) 
  
end MultCommutativeMonoid