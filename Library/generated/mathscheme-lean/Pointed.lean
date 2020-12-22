import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Pointed   
  structure Pointed  (A : Type) : Type := 
       (e : A) 
  
  open Pointed
  structure Sig  (AS : Type) : Type := 
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (Pointed A1)) (Po2 : (Pointed A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Po1)) = (e Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (Pointed A1)) (Po2 : (Pointed A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Po1) (e Po2))) 
  
  inductive PointedTerm   : Type  
     | eL : PointedTerm  
      open PointedTerm 
  
  inductive ClPointedTerm  (A : Type) : Type  
     | sing : (A → ClPointedTerm) 
     | eCl : ClPointedTerm  
      open ClPointedTerm 
  
  inductive OpPointedTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedTerm) 
     | eOL : OpPointedTerm  
      open OpPointedTerm 
  
  inductive OpPointedTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedTerm2) 
     | sing2 : (A → OpPointedTerm2) 
     | eOL2 : OpPointedTerm2  
      open OpPointedTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointedTerm A) → (ClPointedTerm A)) 
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointedTerm n) → (OpPointedTerm n)) 
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointedTerm2 n A) → (OpPointedTerm2 n A)) 
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Pointed A) → (PointedTerm → A)) 
  | Po eL := (e Po)  
  def evalCl   {A : Type}  : ((Pointed A) → ((ClPointedTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po eCl := (e Po)  
  def evalOpB   {A : Type} (n : ℕ)  : ((Pointed A) → ((vector A n) → ((OpPointedTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars eOL := (e Po)  
  def evalOp   {A : Type} (n : ℕ)  : ((Pointed A) → ((vector A n) → ((OpPointedTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars eOL2 := (e Po)  
  def inductionB   (P : (PointedTerm → Type))  : ((P eL) → (∀ (x : PointedTerm) , (P x))) 
  | pel eL := pel  
  def inductionCl   (A : Type) (P : ((ClPointedTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → (∀ (x : (ClPointedTerm A)) , (P x)))) 
  | psing pecl (sing x1) := (psing x1)  
  | psing pecl eCl := pecl  
  def inductionOpB   (n : ℕ) (P : ((OpPointedTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → (∀ (x : (OpPointedTerm n)) , (P x)))) 
  | pv peol (v x1) := (pv x1)  
  | pv peol eOL := peol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointedTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → (∀ (x : (OpPointedTerm2 n A)) , (P x))))) 
  | pv2 psing2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 eOL2 := peol2  
  def stageB  : (PointedTerm → (Staged PointedTerm))
  | eL := (Now eL)  
  def stageCl   (A : Type)  : ((ClPointedTerm A) → (Staged (ClPointedTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  def stageOpB   (n : ℕ)  : ((OpPointedTerm n) → (Staged (OpPointedTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointedTerm2 n A) → (Staged (OpPointedTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A)) 
  
end Pointed