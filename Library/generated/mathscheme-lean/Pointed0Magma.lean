import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Pointed0Magma   
  structure Pointed0Magma  (A : Type) : Type := 
       (zero : A)
       (op : (A → (A → A))) 
  
  open Pointed0Magma
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (Pointed0Magma A1)) (Po2 : (Pointed0Magma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Po1)) = (zero Po2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Po1) x1 x2)) = ((op Po2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (Pointed0Magma A1)) (Po2 : (Pointed0Magma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Po1) (zero Po2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2)))))) 
  
  inductive Pointed0MagmaTerm   : Type  
     | zeroL : Pointed0MagmaTerm 
     | opL : (Pointed0MagmaTerm → (Pointed0MagmaTerm → Pointed0MagmaTerm))  
      open Pointed0MagmaTerm 
  
  inductive ClPointed0MagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointed0MagmaTerm) 
     | zeroCl : ClPointed0MagmaTerm 
     | opCl : (ClPointed0MagmaTerm → (ClPointed0MagmaTerm → ClPointed0MagmaTerm))  
      open ClPointed0MagmaTerm 
  
  inductive OpPointed0MagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointed0MagmaTerm) 
     | zeroOL : OpPointed0MagmaTerm 
     | opOL : (OpPointed0MagmaTerm → (OpPointed0MagmaTerm → OpPointed0MagmaTerm))  
      open OpPointed0MagmaTerm 
  
  inductive OpPointed0MagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointed0MagmaTerm2) 
     | sing2 : (A → OpPointed0MagmaTerm2) 
     | zeroOL2 : OpPointed0MagmaTerm2 
     | opOL2 : (OpPointed0MagmaTerm2 → (OpPointed0MagmaTerm2 → OpPointed0MagmaTerm2))  
      open OpPointed0MagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointed0MagmaTerm A) → (ClPointed0MagmaTerm A)) 
  | zeroCl := zeroCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointed0MagmaTerm n) → (OpPointed0MagmaTerm n)) 
  | zeroOL := zeroOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointed0MagmaTerm2 n A) → (OpPointed0MagmaTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Pointed0Magma A) → (Pointed0MagmaTerm → A)) 
  | Po zeroL := (zero Po)  
  | Po (opL x1 x2) := ((op Po) (evalB Po x1) (evalB Po x2))  
  def evalCl   {A : Type}  : ((Pointed0Magma A) → ((ClPointed0MagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po zeroCl := (zero Po)  
  | Po (opCl x1 x2) := ((op Po) (evalCl Po x1) (evalCl Po x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Pointed0Magma A) → ((vector A n) → ((OpPointed0MagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars zeroOL := (zero Po)  
  | Po vars (opOL x1 x2) := ((op Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Pointed0Magma A) → ((vector A n) → ((OpPointed0MagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars zeroOL2 := (zero Po)  
  | Po vars (opOL2 x1 x2) := ((op Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  def inductionB   (P : (Pointed0MagmaTerm → Type))  : ((P zeroL) → ((∀ (x1 x2 : Pointed0MagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : Pointed0MagmaTerm) , (P x)))) 
  | p0l popl zeroL := p0l  
  | p0l popl (opL x1 x2) := (popl _ _ (inductionB p0l popl x1) (inductionB p0l popl x2))  
  def inductionCl   (A : Type) (P : ((ClPointed0MagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClPointed0MagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClPointed0MagmaTerm A)) , (P x))))) 
  | psing p0cl popcl (sing x1) := (psing x1)  
  | psing p0cl popcl zeroCl := p0cl  
  | psing p0cl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing p0cl popcl x1) (inductionCl psing p0cl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpPointed0MagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpPointed0MagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpPointed0MagmaTerm n)) , (P x))))) 
  | pv p0ol popol (v x1) := (pv x1)  
  | pv p0ol popol zeroOL := p0ol  
  | pv p0ol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv p0ol popol x1) (inductionOpB pv p0ol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointed0MagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpPointed0MagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpPointed0MagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 p0ol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 popol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 p0ol2 popol2 x1) (inductionOp pv2 psing2 p0ol2 popol2 x2))  
  def stageB  : (Pointed0MagmaTerm → (Staged Pointed0MagmaTerm))
  | zeroL := (Now zeroL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClPointed0MagmaTerm A) → (Staged (ClPointed0MagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpPointed0MagmaTerm n) → (Staged (OpPointed0MagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointed0MagmaTerm2 n A) → (Staged (OpPointed0MagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Pointed0Magma