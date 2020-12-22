import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedOne   
  structure PointedOne  (A : Type) : Type := 
       (one : A) 
  
  open PointedOne
  structure Sig  (AS : Type) : Type := 
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedOne A1)) (Po2 : (PointedOne A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one Po1)) = (one Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedOne A1)) (Po2 : (PointedOne A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one Po1) (one Po2))) 
  
  inductive PointedOneTerm   : Type  
     | oneL : PointedOneTerm  
      open PointedOneTerm 
  
  inductive ClPointedOneTerm  (A : Type) : Type  
     | sing : (A → ClPointedOneTerm) 
     | oneCl : ClPointedOneTerm  
      open ClPointedOneTerm 
  
  inductive OpPointedOneTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedOneTerm) 
     | oneOL : OpPointedOneTerm  
      open OpPointedOneTerm 
  
  inductive OpPointedOneTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedOneTerm2) 
     | sing2 : (A → OpPointedOneTerm2) 
     | oneOL2 : OpPointedOneTerm2  
      open OpPointedOneTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointedOneTerm A) → (ClPointedOneTerm A)) 
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointedOneTerm n) → (OpPointedOneTerm n)) 
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointedOneTerm2 n A) → (OpPointedOneTerm2 n A)) 
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedOne A) → (PointedOneTerm → A)) 
  | Po oneL := (one Po)  
  def evalCl   {A : Type}  : ((PointedOne A) → ((ClPointedOneTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po oneCl := (one Po)  
  def evalOpB   {A : Type} (n : ℕ)  : ((PointedOne A) → ((vector A n) → ((OpPointedOneTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars oneOL := (one Po)  
  def evalOp   {A : Type} (n : ℕ)  : ((PointedOne A) → ((vector A n) → ((OpPointedOneTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars oneOL2 := (one Po)  
  def inductionB   (P : (PointedOneTerm → Type))  : ((P oneL) → (∀ (x : PointedOneTerm) , (P x))) 
  | p1l oneL := p1l  
  def inductionCl   (A : Type) (P : ((ClPointedOneTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → (∀ (x : (ClPointedOneTerm A)) , (P x)))) 
  | psing p1cl (sing x1) := (psing x1)  
  | psing p1cl oneCl := p1cl  
  def inductionOpB   (n : ℕ) (P : ((OpPointedOneTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → (∀ (x : (OpPointedOneTerm n)) , (P x)))) 
  | pv p1ol (v x1) := (pv x1)  
  | pv p1ol oneOL := p1ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointedOneTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → (∀ (x : (OpPointedOneTerm2 n A)) , (P x))))) 
  | pv2 psing2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (PointedOneTerm → (Staged PointedOneTerm))
  | oneL := (Now oneL)  
  def stageCl   (A : Type)  : ((ClPointedOneTerm A) → (Staged (ClPointedOneTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  def stageOpB   (n : ℕ)  : ((OpPointedOneTerm n) → (Staged (OpPointedOneTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointedOneTerm2 n A) → (Staged (OpPointedOneTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A)) 
  
end PointedOne