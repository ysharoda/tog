import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MedialMagma   
  structure MedialMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (mediates : (∀ {w x y z : A} , (op (op x y) (op z w)) = (op (op x z) (op y w)))) 
  
  open MedialMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (mediatesP : (∀ {wP xP yP zP : (Prod A A)} , (opP (opP xP yP) (opP zP wP)) = (opP (opP xP zP) (opP yP wP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Me1 : (MedialMagma A1)) (Me2 : (MedialMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Me1) x1 x2)) = ((op Me2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Me1 : (MedialMagma A1)) (Me2 : (MedialMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Me1) x1 x2) ((op Me2) y1 y2)))))) 
  
  inductive MedialMagmaTerm   : Type  
     | opL : (MedialMagmaTerm → (MedialMagmaTerm → MedialMagmaTerm))  
      open MedialMagmaTerm 
  
  inductive ClMedialMagmaTerm  (A : Type) : Type  
     | sing : (A → ClMedialMagmaTerm) 
     | opCl : (ClMedialMagmaTerm → (ClMedialMagmaTerm → ClMedialMagmaTerm))  
      open ClMedialMagmaTerm 
  
  inductive OpMedialMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMedialMagmaTerm) 
     | opOL : (OpMedialMagmaTerm → (OpMedialMagmaTerm → OpMedialMagmaTerm))  
      open OpMedialMagmaTerm 
  
  inductive OpMedialMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMedialMagmaTerm2) 
     | sing2 : (A → OpMedialMagmaTerm2) 
     | opOL2 : (OpMedialMagmaTerm2 → (OpMedialMagmaTerm2 → OpMedialMagmaTerm2))  
      open OpMedialMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMedialMagmaTerm A) → (ClMedialMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMedialMagmaTerm n) → (OpMedialMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMedialMagmaTerm2 n A) → (OpMedialMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MedialMagma A) → (MedialMagmaTerm → A)) 
  | Me (opL x1 x2) := ((op Me) (evalB Me x1) (evalB Me x2))  
  def evalCl   {A : Type}  : ((MedialMagma A) → ((ClMedialMagmaTerm A) → A)) 
  | Me (sing x1) := x1  
  | Me (opCl x1 x2) := ((op Me) (evalCl Me x1) (evalCl Me x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MedialMagma A) → ((vector A n) → ((OpMedialMagmaTerm n) → A))) 
  | Me vars (v x1) := (nth vars x1)  
  | Me vars (opOL x1 x2) := ((op Me) (evalOpB Me vars x1) (evalOpB Me vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((MedialMagma A) → ((vector A n) → ((OpMedialMagmaTerm2 n A) → A))) 
  | Me vars (v2 x1) := (nth vars x1)  
  | Me vars (sing2 x1) := x1  
  | Me vars (opOL2 x1 x2) := ((op Me) (evalOp Me vars x1) (evalOp Me vars x2))  
  def inductionB   (P : (MedialMagmaTerm → Type))  : ((∀ (x1 x2 : MedialMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : MedialMagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClMedialMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMedialMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClMedialMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpMedialMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMedialMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpMedialMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMedialMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMedialMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpMedialMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (MedialMagmaTerm → (Staged MedialMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClMedialMagmaTerm A) → (Staged (ClMedialMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpMedialMagmaTerm n) → (Staged (OpMedialMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMedialMagmaTerm2 n A) → (Staged (OpMedialMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MedialMagma