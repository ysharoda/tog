import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedZero   
  structure PointedZero  (A : Type) : Type := 
       (zero : A) 
  
  open PointedZero
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedZero A1)) (Po2 : (PointedZero A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Po1)) = (zero Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedZero A1)) (Po2 : (PointedZero A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Po1) (zero Po2))) 
  
  inductive PointedZeroTerm   : Type  
     | zeroL : PointedZeroTerm  
      open PointedZeroTerm 
  
  inductive ClPointedZeroTerm  (A : Type) : Type  
     | sing : (A → ClPointedZeroTerm) 
     | zeroCl : ClPointedZeroTerm  
      open ClPointedZeroTerm 
  
  inductive OpPointedZeroTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedZeroTerm) 
     | zeroOL : OpPointedZeroTerm  
      open OpPointedZeroTerm 
  
  inductive OpPointedZeroTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedZeroTerm2) 
     | sing2 : (A → OpPointedZeroTerm2) 
     | zeroOL2 : OpPointedZeroTerm2  
      open OpPointedZeroTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPointedZeroTerm A) → (ClPointedZeroTerm A)) 
  | zeroCl := zeroCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPointedZeroTerm n) → (OpPointedZeroTerm n)) 
  | zeroOL := zeroOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPointedZeroTerm2 n A) → (OpPointedZeroTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedZero A) → (PointedZeroTerm → A)) 
  | Po zeroL := (zero Po)  
  def evalCl   {A : Type}  : ((PointedZero A) → ((ClPointedZeroTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po zeroCl := (zero Po)  
  def evalOpB   {A : Type} {n : ℕ}  : ((PointedZero A) → ((vector A n) → ((OpPointedZeroTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars zeroOL := (zero Po)  
  def evalOp   {A : Type} {n : ℕ}  : ((PointedZero A) → ((vector A n) → ((OpPointedZeroTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars zeroOL2 := (zero Po)  
  def inductionB   {P : (PointedZeroTerm → Type)}  : ((P zeroL) → (∀ (x : PointedZeroTerm) , (P x))) 
  | p0l zeroL := p0l  
  def inductionCl   {A : Type} {P : ((ClPointedZeroTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → (∀ (x : (ClPointedZeroTerm A)) , (P x)))) 
  | psing p0cl (sing x1) := (psing x1)  
  | psing p0cl zeroCl := p0cl  
  def inductionOpB   {n : ℕ} {P : ((OpPointedZeroTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → (∀ (x : (OpPointedZeroTerm n)) , (P x)))) 
  | pv p0ol (v x1) := (pv x1)  
  | pv p0ol zeroOL := p0ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPointedZeroTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → (∀ (x : (OpPointedZeroTerm2 n A)) , (P x))))) 
  | pv2 psing2 p0ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 zeroOL2 := p0ol2  
  def stageB  : (PointedZeroTerm → (Staged PointedZeroTerm))
  | zeroL := (Now zeroL)  
  def stageCl   {A : Type}  : ((ClPointedZeroTerm A) → (Staged (ClPointedZeroTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  def stageOpB   {n : ℕ}  : ((OpPointedZeroTerm n) → (Staged (OpPointedZeroTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPointedZeroTerm2 n A) → (Staged (OpPointedZeroTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A)) 
  
end PointedZero