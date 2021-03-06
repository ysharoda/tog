import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Magma   
  structure Magma  (A : Type) : Type := 
       (op : (A → (A → A))) 
  
  open Magma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ma1 : (Magma A1)) (Ma2 : (Magma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ma1) x1 x2)) = ((op Ma2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ma1 : (Magma A1)) (Ma2 : (Magma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ma1) x1 x2) ((op Ma2) y1 y2)))))) 
  
  inductive MagmaTerm   : Type  
     | opL : (MagmaTerm → (MagmaTerm → MagmaTerm))  
      open MagmaTerm 
  
  inductive ClMagmaTerm  (A : Type) : Type  
     | sing : (A → ClMagmaTerm) 
     | opCl : (ClMagmaTerm → (ClMagmaTerm → ClMagmaTerm))  
      open ClMagmaTerm 
  
  inductive OpMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMagmaTerm) 
     | opOL : (OpMagmaTerm → (OpMagmaTerm → OpMagmaTerm))  
      open OpMagmaTerm 
  
  inductive OpMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMagmaTerm2) 
     | sing2 : (A → OpMagmaTerm2) 
     | opOL2 : (OpMagmaTerm2 → (OpMagmaTerm2 → OpMagmaTerm2))  
      open OpMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMagmaTerm A) → (ClMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMagmaTerm n) → (OpMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMagmaTerm2 n A) → (OpMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Magma A) → (MagmaTerm → A)) 
  | Ma (opL x1 x2) := ((op Ma) (evalB Ma x1) (evalB Ma x2))  
  def evalCl   {A : Type}  : ((Magma A) → ((ClMagmaTerm A) → A)) 
  | Ma (sing x1) := x1  
  | Ma (opCl x1 x2) := ((op Ma) (evalCl Ma x1) (evalCl Ma x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Magma A) → ((vector A n) → ((OpMagmaTerm n) → A))) 
  | Ma vars (v x1) := (nth vars x1)  
  | Ma vars (opOL x1 x2) := ((op Ma) (evalOpB Ma vars x1) (evalOpB Ma vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Magma A) → ((vector A n) → ((OpMagmaTerm2 n A) → A))) 
  | Ma vars (v2 x1) := (nth vars x1)  
  | Ma vars (sing2 x1) := x1  
  | Ma vars (opOL2 x1 x2) := ((op Ma) (evalOp Ma vars x1) (evalOp Ma vars x2))  
  def inductionB   {P : (MagmaTerm → Type)}  : ((∀ (x1 x2 : MagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : MagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (MagmaTerm → (Staged MagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMagmaTerm A) → (Staged (ClMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMagmaTerm n) → (Staged (OpMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMagmaTerm2 n A) → (Staged (OpMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Magma