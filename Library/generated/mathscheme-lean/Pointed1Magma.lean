import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Pointed1Magma   
  structure Pointed1Magma  (A : Type) : Type := 
       (one : A)
       (op : (A → (A → A))) 
  
  open Pointed1Magma
  structure Sig  (AS : Type) : Type := 
       (oneS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (Pointed1Magma A1)) (Po2 : (Pointed1Magma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one Po1)) = (one Po2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Po1) x1 x2)) = ((op Po2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (Pointed1Magma A1)) (Po2 : (Pointed1Magma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one Po1) (one Po2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2)))))) 
  
  inductive Pointed1MagmaTerm   : Type  
     | oneL : Pointed1MagmaTerm 
     | opL : (Pointed1MagmaTerm → (Pointed1MagmaTerm → Pointed1MagmaTerm))  
      open Pointed1MagmaTerm 
  
  inductive ClPointed1MagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointed1MagmaTerm) 
     | oneCl : ClPointed1MagmaTerm 
     | opCl : (ClPointed1MagmaTerm → (ClPointed1MagmaTerm → ClPointed1MagmaTerm))  
      open ClPointed1MagmaTerm 
  
  inductive OpPointed1MagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointed1MagmaTerm) 
     | oneOL : OpPointed1MagmaTerm 
     | opOL : (OpPointed1MagmaTerm → (OpPointed1MagmaTerm → OpPointed1MagmaTerm))  
      open OpPointed1MagmaTerm 
  
  inductive OpPointed1MagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointed1MagmaTerm2) 
     | sing2 : (A → OpPointed1MagmaTerm2) 
     | oneOL2 : OpPointed1MagmaTerm2 
     | opOL2 : (OpPointed1MagmaTerm2 → (OpPointed1MagmaTerm2 → OpPointed1MagmaTerm2))  
      open OpPointed1MagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointed1MagmaTerm A) → (ClPointed1MagmaTerm A)) 
  | oneCl := oneCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointed1MagmaTerm n) → (OpPointed1MagmaTerm n)) 
  | oneOL := oneOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointed1MagmaTerm2 n A) → (OpPointed1MagmaTerm2 n A)) 
  | oneOL2 := oneOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Pointed1Magma A) → (Pointed1MagmaTerm → A)) 
  | Po oneL := (one Po)  
  | Po (opL x1 x2) := ((op Po) (evalB Po x1) (evalB Po x2))  
  def evalCl   {A : Type}  : ((Pointed1Magma A) → ((ClPointed1MagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po oneCl := (one Po)  
  | Po (opCl x1 x2) := ((op Po) (evalCl Po x1) (evalCl Po x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Pointed1Magma A) → ((vector A n) → ((OpPointed1MagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars oneOL := (one Po)  
  | Po vars (opOL x1 x2) := ((op Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Pointed1Magma A) → ((vector A n) → ((OpPointed1MagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars oneOL2 := (one Po)  
  | Po vars (opOL2 x1 x2) := ((op Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  def inductionB   (P : (Pointed1MagmaTerm → Type))  : ((P oneL) → ((∀ (x1 x2 : Pointed1MagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : Pointed1MagmaTerm) , (P x)))) 
  | p1l popl oneL := p1l  
  | p1l popl (opL x1 x2) := (popl _ _ (inductionB p1l popl x1) (inductionB p1l popl x2))  
  def inductionCl   (A : Type) (P : ((ClPointed1MagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → ((∀ (x1 x2 : (ClPointed1MagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClPointed1MagmaTerm A)) , (P x))))) 
  | psing p1cl popcl (sing x1) := (psing x1)  
  | psing p1cl popcl oneCl := p1cl  
  | psing p1cl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing p1cl popcl x1) (inductionCl psing p1cl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpPointed1MagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → ((∀ (x1 x2 : (OpPointed1MagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpPointed1MagmaTerm n)) , (P x))))) 
  | pv p1ol popol (v x1) := (pv x1)  
  | pv p1ol popol oneOL := p1ol  
  | pv p1ol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv p1ol popol x1) (inductionOpB pv p1ol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointed1MagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → ((∀ (x1 x2 : (OpPointed1MagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpPointed1MagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 p1ol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 popol2 oneOL2 := p1ol2  
  | pv2 psing2 p1ol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 p1ol2 popol2 x1) (inductionOp pv2 psing2 p1ol2 popol2 x2))  
  def stageB  : (Pointed1MagmaTerm → (Staged Pointed1MagmaTerm))
  | oneL := (Now oneL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClPointed1MagmaTerm A) → (Staged (ClPointed1MagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpPointed1MagmaTerm n) → (Staged (OpPointed1MagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointed1MagmaTerm2 n A) → (Staged (OpPointed1MagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Pointed1Magma