import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CommutativeMagma   
  structure CommutativeMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x))) 
  
  open CommutativeMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (CommutativeMagma A1)) (Co2 : (CommutativeMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Co1) x1 x2)) = ((op Co2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (CommutativeMagma A1)) (Co2 : (CommutativeMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2)))))) 
  
  inductive CommutativeMagmaTerm   : Type  
     | opL : (CommutativeMagmaTerm → (CommutativeMagmaTerm → CommutativeMagmaTerm))  
      open CommutativeMagmaTerm 
  
  inductive ClCommutativeMagmaTerm  (A : Type) : Type  
     | sing : (A → ClCommutativeMagmaTerm) 
     | opCl : (ClCommutativeMagmaTerm → (ClCommutativeMagmaTerm → ClCommutativeMagmaTerm))  
      open ClCommutativeMagmaTerm 
  
  inductive OpCommutativeMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCommutativeMagmaTerm) 
     | opOL : (OpCommutativeMagmaTerm → (OpCommutativeMagmaTerm → OpCommutativeMagmaTerm))  
      open OpCommutativeMagmaTerm 
  
  inductive OpCommutativeMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCommutativeMagmaTerm2) 
     | sing2 : (A → OpCommutativeMagmaTerm2) 
     | opOL2 : (OpCommutativeMagmaTerm2 → (OpCommutativeMagmaTerm2 → OpCommutativeMagmaTerm2))  
      open OpCommutativeMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClCommutativeMagmaTerm A) → (ClCommutativeMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpCommutativeMagmaTerm n) → (OpCommutativeMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpCommutativeMagmaTerm2 n A) → (OpCommutativeMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CommutativeMagma A) → (CommutativeMagmaTerm → A)) 
  | Co (opL x1 x2) := ((op Co) (evalB Co x1) (evalB Co x2))  
  def evalCl   {A : Type}  : ((CommutativeMagma A) → ((ClCommutativeMagmaTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co (opCl x1 x2) := ((op Co) (evalCl Co x1) (evalCl Co x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((CommutativeMagma A) → ((vector A n) → ((OpCommutativeMagmaTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars (opOL x1 x2) := ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((CommutativeMagma A) → ((vector A n) → ((OpCommutativeMagmaTerm2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars (opOL2 x1 x2) := ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  def inductionB   (P : (CommutativeMagmaTerm → Type))  : ((∀ (x1 x2 : CommutativeMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : CommutativeMagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClCommutativeMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCommutativeMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClCommutativeMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpCommutativeMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCommutativeMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpCommutativeMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpCommutativeMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCommutativeMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpCommutativeMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (CommutativeMagmaTerm → (Staged CommutativeMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClCommutativeMagmaTerm A) → (Staged (ClCommutativeMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpCommutativeMagmaTerm n) → (Staged (OpCommutativeMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpCommutativeMagmaTerm2 n A) → (Staged (OpCommutativeMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end CommutativeMagma