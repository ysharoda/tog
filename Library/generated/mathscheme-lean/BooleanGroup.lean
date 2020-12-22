import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BooleanGroup   
  structure BooleanGroup  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (runit_e : (∀ {x : A} , (op x e) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (unipotence : (∀ {x : A} , (op x x) = e)) 
  
  open BooleanGroup
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (unipotenceP : (∀ {xP : (Prod A A)} , (opP xP xP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BooleanGroup A1)) (Bo2 : (BooleanGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Bo1)) = (e Bo2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Bo1) x1 x2)) = ((op Bo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BooleanGroup A1)) (Bo2 : (BooleanGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Bo1) (e Bo2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Bo1) x1 x2) ((op Bo2) y1 y2)))))) 
  
  inductive BooleanGroupTerm   : Type  
     | eL : BooleanGroupTerm 
     | opL : (BooleanGroupTerm → (BooleanGroupTerm → BooleanGroupTerm))  
      open BooleanGroupTerm 
  
  inductive ClBooleanGroupTerm  (A : Type) : Type  
     | sing : (A → ClBooleanGroupTerm) 
     | eCl : ClBooleanGroupTerm 
     | opCl : (ClBooleanGroupTerm → (ClBooleanGroupTerm → ClBooleanGroupTerm))  
      open ClBooleanGroupTerm 
  
  inductive OpBooleanGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBooleanGroupTerm) 
     | eOL : OpBooleanGroupTerm 
     | opOL : (OpBooleanGroupTerm → (OpBooleanGroupTerm → OpBooleanGroupTerm))  
      open OpBooleanGroupTerm 
  
  inductive OpBooleanGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBooleanGroupTerm2) 
     | sing2 : (A → OpBooleanGroupTerm2) 
     | eOL2 : OpBooleanGroupTerm2 
     | opOL2 : (OpBooleanGroupTerm2 → (OpBooleanGroupTerm2 → OpBooleanGroupTerm2))  
      open OpBooleanGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClBooleanGroupTerm A) → (ClBooleanGroupTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x eCl) := x  
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpBooleanGroupTerm n) → (OpBooleanGroupTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x eOL) := x  
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpBooleanGroupTerm2 n A) → (OpBooleanGroupTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x eOL2) := x  
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BooleanGroup A) → (BooleanGroupTerm → A)) 
  | Bo eL := (e Bo)  
  | Bo (opL x1 x2) := ((op Bo) (evalB Bo x1) (evalB Bo x2))  
  def evalCl   {A : Type}  : ((BooleanGroup A) → ((ClBooleanGroupTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo eCl := (e Bo)  
  | Bo (opCl x1 x2) := ((op Bo) (evalCl Bo x1) (evalCl Bo x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((BooleanGroup A) → ((vector A n) → ((OpBooleanGroupTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars eOL := (e Bo)  
  | Bo vars (opOL x1 x2) := ((op Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((BooleanGroup A) → ((vector A n) → ((OpBooleanGroupTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars eOL2 := (e Bo)  
  | Bo vars (opOL2 x1 x2) := ((op Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  def inductionB   (P : (BooleanGroupTerm → Type))  : ((P eL) → ((∀ (x1 x2 : BooleanGroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : BooleanGroupTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   (A : Type) (P : ((ClBooleanGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClBooleanGroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClBooleanGroupTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpBooleanGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpBooleanGroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpBooleanGroupTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpBooleanGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpBooleanGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpBooleanGroupTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (BooleanGroupTerm → (Staged BooleanGroupTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClBooleanGroupTerm A) → (Staged (ClBooleanGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpBooleanGroupTerm n) → (Staged (OpBooleanGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpBooleanGroupTerm2 n A) → (Staged (OpBooleanGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end BooleanGroup