import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Unital   
  structure Unital  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (runit_e : (∀ {x : A} , (op x e) = x)) 
  
  open Unital
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Un1 : (Unital A1)) (Un2 : (Unital A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Un1)) = (e Un2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Un1) x1 x2)) = ((op Un2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Un1 : (Unital A1)) (Un2 : (Unital A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Un1) (e Un2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Un1) x1 x2) ((op Un2) y1 y2)))))) 
  
  inductive UnitalTerm   : Type  
     | eL : UnitalTerm 
     | opL : (UnitalTerm → (UnitalTerm → UnitalTerm))  
      open UnitalTerm 
  
  inductive ClUnitalTerm  (A : Type) : Type  
     | sing : (A → ClUnitalTerm) 
     | eCl : ClUnitalTerm 
     | opCl : (ClUnitalTerm → (ClUnitalTerm → ClUnitalTerm))  
      open ClUnitalTerm 
  
  inductive OpUnitalTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpUnitalTerm) 
     | eOL : OpUnitalTerm 
     | opOL : (OpUnitalTerm → (OpUnitalTerm → OpUnitalTerm))  
      open OpUnitalTerm 
  
  inductive OpUnitalTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpUnitalTerm2) 
     | sing2 : (A → OpUnitalTerm2) 
     | eOL2 : OpUnitalTerm2 
     | opOL2 : (OpUnitalTerm2 → (OpUnitalTerm2 → OpUnitalTerm2))  
      open OpUnitalTerm2 
  
  def simplifyCl   {A : Type}  : ((ClUnitalTerm A) → (ClUnitalTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x eCl) := x  
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpUnitalTerm n) → (OpUnitalTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x eOL) := x  
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpUnitalTerm2 n A) → (OpUnitalTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x eOL2) := x  
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Unital A) → (UnitalTerm → A)) 
  | Un eL := (e Un)  
  | Un (opL x1 x2) := ((op Un) (evalB Un x1) (evalB Un x2))  
  def evalCl   {A : Type}  : ((Unital A) → ((ClUnitalTerm A) → A)) 
  | Un (sing x1) := x1  
  | Un eCl := (e Un)  
  | Un (opCl x1 x2) := ((op Un) (evalCl Un x1) (evalCl Un x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Unital A) → ((vector A n) → ((OpUnitalTerm n) → A))) 
  | Un vars (v x1) := (nth vars x1)  
  | Un vars eOL := (e Un)  
  | Un vars (opOL x1 x2) := ((op Un) (evalOpB Un vars x1) (evalOpB Un vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Unital A) → ((vector A n) → ((OpUnitalTerm2 n A) → A))) 
  | Un vars (v2 x1) := (nth vars x1)  
  | Un vars (sing2 x1) := x1  
  | Un vars eOL2 := (e Un)  
  | Un vars (opOL2 x1 x2) := ((op Un) (evalOp Un vars x1) (evalOp Un vars x2))  
  def inductionB   {P : (UnitalTerm → Type)}  : ((P eL) → ((∀ (x1 x2 : UnitalTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : UnitalTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   {A : Type} {P : ((ClUnitalTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClUnitalTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClUnitalTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpUnitalTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpUnitalTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpUnitalTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpUnitalTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpUnitalTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpUnitalTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (UnitalTerm → (Staged UnitalTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClUnitalTerm A) → (Staged (ClUnitalTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpUnitalTerm n) → (Staged (OpUnitalTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpUnitalTerm2 n A) → (Staged (OpUnitalTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Unital