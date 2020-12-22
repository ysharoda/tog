import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Group   
  structure Group  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (runit_e : (∀ {x : A} , (op x e) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (inv : (A → A))
       (leftInverse_inv_op_e : (∀ {x : A} , (op x (inv x)) = e))
       (rightInverse_inv_op_e : (∀ {x : A} , (op (inv x) x) = e)) 
  
  open Group
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS)))
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (invP : ((Prod A A) → (Prod A A)))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (leftInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP xP (invP xP)) = eP))
       (rightInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (invP xP) xP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Gr1 : (Group A1)) (Gr2 : (Group A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Gr1)) = (e Gr2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Gr1) x1 x2)) = ((op Gr2) (hom x1) (hom x2))))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Gr1) x1)) = ((inv Gr2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Gr1 : (Group A1)) (Gr2 : (Group A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Gr1) (e Gr2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Gr1) x1 x2) ((op Gr2) y1 y2))))))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Gr1) x1) ((inv Gr2) y1))))) 
  
  inductive GroupTerm   : Type  
     | eL : GroupTerm 
     | opL : (GroupTerm → (GroupTerm → GroupTerm)) 
     | invL : (GroupTerm → GroupTerm)  
      open GroupTerm 
  
  inductive ClGroupTerm  (A : Type) : Type  
     | sing : (A → ClGroupTerm) 
     | eCl : ClGroupTerm 
     | opCl : (ClGroupTerm → (ClGroupTerm → ClGroupTerm)) 
     | invCl : (ClGroupTerm → ClGroupTerm)  
      open ClGroupTerm 
  
  inductive OpGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpGroupTerm) 
     | eOL : OpGroupTerm 
     | opOL : (OpGroupTerm → (OpGroupTerm → OpGroupTerm)) 
     | invOL : (OpGroupTerm → OpGroupTerm)  
      open OpGroupTerm 
  
  inductive OpGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpGroupTerm2) 
     | sing2 : (A → OpGroupTerm2) 
     | eOL2 : OpGroupTerm2 
     | opOL2 : (OpGroupTerm2 → (OpGroupTerm2 → OpGroupTerm2)) 
     | invOL2 : (OpGroupTerm2 → OpGroupTerm2)  
      open OpGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClGroupTerm A) → (ClGroupTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x eCl) := x  
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpGroupTerm n) → (OpGroupTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x eOL) := x  
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpGroupTerm2 n A) → (OpGroupTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x eOL2) := x  
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Group A) → (GroupTerm → A)) 
  | Gr eL := (e Gr)  
  | Gr (opL x1 x2) := ((op Gr) (evalB Gr x1) (evalB Gr x2))  
  | Gr (invL x1) := ((inv Gr) (evalB Gr x1))  
  def evalCl   {A : Type}  : ((Group A) → ((ClGroupTerm A) → A)) 
  | Gr (sing x1) := x1  
  | Gr eCl := (e Gr)  
  | Gr (opCl x1 x2) := ((op Gr) (evalCl Gr x1) (evalCl Gr x2))  
  | Gr (invCl x1) := ((inv Gr) (evalCl Gr x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Group A) → ((vector A n) → ((OpGroupTerm n) → A))) 
  | Gr vars (v x1) := (nth vars x1)  
  | Gr vars eOL := (e Gr)  
  | Gr vars (opOL x1 x2) := ((op Gr) (evalOpB Gr vars x1) (evalOpB Gr vars x2))  
  | Gr vars (invOL x1) := ((inv Gr) (evalOpB Gr vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((Group A) → ((vector A n) → ((OpGroupTerm2 n A) → A))) 
  | Gr vars (v2 x1) := (nth vars x1)  
  | Gr vars (sing2 x1) := x1  
  | Gr vars eOL2 := (e Gr)  
  | Gr vars (opOL2 x1 x2) := ((op Gr) (evalOp Gr vars x1) (evalOp Gr vars x2))  
  | Gr vars (invOL2 x1) := ((inv Gr) (evalOp Gr vars x1))  
  def inductionB   (P : (GroupTerm → Type))  : ((P eL) → ((∀ (x1 x2 : GroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((∀ (x1 : GroupTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : GroupTerm) , (P x))))) 
  | pel popl pinvl eL := pel  
  | pel popl pinvl (opL x1 x2) := (popl _ _ (inductionB pel popl pinvl x1) (inductionB pel popl pinvl x2))  
  | pel popl pinvl (invL x1) := (pinvl _ (inductionB pel popl pinvl x1))  
  def inductionCl   (A : Type) (P : ((ClGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClGroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((∀ (x1 : (ClGroupTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClGroupTerm A)) , (P x)))))) 
  | psing pecl popcl pinvcl (sing x1) := (psing x1)  
  | psing pecl popcl pinvcl eCl := pecl  
  | psing pecl popcl pinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl pinvcl x1) (inductionCl psing pecl popcl pinvcl x2))  
  | psing pecl popcl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing pecl popcl pinvcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpGroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((∀ (x1 : (OpGroupTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpGroupTerm n)) , (P x)))))) 
  | pv peol popol pinvol (v x1) := (pv x1)  
  | pv peol popol pinvol eOL := peol  
  | pv peol popol pinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol pinvol x1) (inductionOpB pv peol popol pinvol x2))  
  | pv peol popol pinvol (invOL x1) := (pinvol _ (inductionOpB pv peol popol pinvol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((∀ (x1 : (OpGroupTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 peol2 popol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 pinvol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 pinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 pinvol2 x1) (inductionOp pv2 psing2 peol2 popol2 pinvol2 x2))  
  | pv2 psing2 peol2 popol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 peol2 popol2 pinvol2 x1))  
  def stageB  : (GroupTerm → (Staged GroupTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClGroupTerm A) → (Staged (ClGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpGroupTerm n) → (Staged (OpGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpGroupTerm2 n A) → (Staged (OpGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (invT : ((Repr A) → (Repr A))) 
  
end Group