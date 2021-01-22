import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Group1   
  structure Group1  (A : Type) : Type := 
       (op : (A → (A → A)))
       (one : A)
       (lunit_one : (∀ {x : A} , (op one x) = x))
       (runit_one : (∀ {x : A} , (op x one) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (inv : (A → A))
       (leftInverse_inv_op_one : (∀ {x : A} , (op x (inv x)) = one))
       (rightInverse_inv_op_one : (∀ {x : A} , (op (inv x) x) = one)) 
  
  open Group1
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (oneS : AS)
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (invP : ((Prod A A) → (Prod A A)))
       (lunit_1P : (∀ {xP : (Prod A A)} , (opP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (opP xP oneP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (leftInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (opP xP (invP xP)) = oneP))
       (rightInverse_inv_op_1P : (∀ {xP : (Prod A A)} , (opP (invP xP) xP) = oneP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Gr1 : (Group1 A1)) (Gr2 : (Group1 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Gr1) x1 x2)) = ((op Gr2) (hom x1) (hom x2))))
       (pres_one : (hom (one Gr1)) = (one Gr2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Gr1) x1)) = ((inv Gr2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Gr1 : (Group1 A1)) (Gr2 : (Group1 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Gr1) x1 x2) ((op Gr2) y1 y2))))))
       (interp_one : (interp (one Gr1) (one Gr2)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Gr1) x1) ((inv Gr2) y1))))) 
  
  inductive Group1LTerm   : Type  
     | opL : (Group1LTerm → (Group1LTerm → Group1LTerm)) 
     | oneL : Group1LTerm 
     | invL : (Group1LTerm → Group1LTerm)  
      open Group1LTerm 
  
  inductive ClGroup1ClTerm  (A : Type) : Type  
     | sing : (A → ClGroup1ClTerm) 
     | opCl : (ClGroup1ClTerm → (ClGroup1ClTerm → ClGroup1ClTerm)) 
     | oneCl : ClGroup1ClTerm 
     | invCl : (ClGroup1ClTerm → ClGroup1ClTerm)  
      open ClGroup1ClTerm 
  
  inductive OpGroup1OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpGroup1OLTerm) 
     | opOL : (OpGroup1OLTerm → (OpGroup1OLTerm → OpGroup1OLTerm)) 
     | oneOL : OpGroup1OLTerm 
     | invOL : (OpGroup1OLTerm → OpGroup1OLTerm)  
      open OpGroup1OLTerm 
  
  inductive OpGroup1OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpGroup1OL2Term2) 
     | sing2 : (A → OpGroup1OL2Term2) 
     | opOL2 : (OpGroup1OL2Term2 → (OpGroup1OL2Term2 → OpGroup1OL2Term2)) 
     | oneOL2 : OpGroup1OL2Term2 
     | invOL2 : (OpGroup1OL2Term2 → OpGroup1OL2Term2)  
      open OpGroup1OL2Term2 
  
  def simplifyCl   {A : Type}  : ((ClGroup1ClTerm A) → (ClGroup1ClTerm A)) 
  | (opCl oneCl x) := x  
  | (opCl x oneCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpGroup1OLTerm n) → (OpGroup1OLTerm n)) 
  | (opOL oneOL x) := x  
  | (opOL x oneOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpGroup1OL2Term2 n A) → (OpGroup1OL2Term2 n A)) 
  | (opOL2 oneOL2 x) := x  
  | (opOL2 x oneOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Group1 A) → (Group1LTerm → A)) 
  | Gr (opL x1 x2) := ((op Gr) (evalB Gr x1) (evalB Gr x2))  
  | Gr oneL := (one Gr)  
  | Gr (invL x1) := ((inv Gr) (evalB Gr x1))  
  def evalCl   {A : Type}  : ((Group1 A) → ((ClGroup1ClTerm A) → A)) 
  | Gr (sing x1) := x1  
  | Gr (opCl x1 x2) := ((op Gr) (evalCl Gr x1) (evalCl Gr x2))  
  | Gr oneCl := (one Gr)  
  | Gr (invCl x1) := ((inv Gr) (evalCl Gr x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Group1 A) → ((vector A n) → ((OpGroup1OLTerm n) → A))) 
  | Gr vars (v x1) := (nth vars x1)  
  | Gr vars (opOL x1 x2) := ((op Gr) (evalOpB Gr vars x1) (evalOpB Gr vars x2))  
  | Gr vars oneOL := (one Gr)  
  | Gr vars (invOL x1) := ((inv Gr) (evalOpB Gr vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((Group1 A) → ((vector A n) → ((OpGroup1OL2Term2 n A) → A))) 
  | Gr vars (v2 x1) := (nth vars x1)  
  | Gr vars (sing2 x1) := x1  
  | Gr vars (opOL2 x1 x2) := ((op Gr) (evalOp Gr vars x1) (evalOp Gr vars x2))  
  | Gr vars oneOL2 := (one Gr)  
  | Gr vars (invOL2 x1) := ((inv Gr) (evalOp Gr vars x1))  
  def inductionB   {P : (Group1LTerm → Type)}  : ((∀ (x1 x2 : Group1LTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P oneL) → ((∀ (x1 : Group1LTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : Group1LTerm) , (P x))))) 
  | popl p1l pinvl (opL x1 x2) := (popl _ _ (inductionB popl p1l pinvl x1) (inductionB popl p1l pinvl x2))  
  | popl p1l pinvl oneL := p1l  
  | popl p1l pinvl (invL x1) := (pinvl _ (inductionB popl p1l pinvl x1))  
  def inductionCl   {A : Type} {P : ((ClGroup1ClTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClGroup1ClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P oneCl) → ((∀ (x1 : (ClGroup1ClTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClGroup1ClTerm A)) , (P x)))))) 
  | psing popcl p1cl pinvcl (sing x1) := (psing x1)  
  | psing popcl p1cl pinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl p1cl pinvcl x1) (inductionCl psing popcl p1cl pinvcl x2))  
  | psing popcl p1cl pinvcl oneCl := p1cl  
  | psing popcl p1cl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing popcl p1cl pinvcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpGroup1OLTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpGroup1OLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P oneOL) → ((∀ (x1 : (OpGroup1OLTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpGroup1OLTerm n)) , (P x)))))) 
  | pv popol p1ol pinvol (v x1) := (pv x1)  
  | pv popol p1ol pinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol p1ol pinvol x1) (inductionOpB pv popol p1ol pinvol x2))  
  | pv popol p1ol pinvol oneOL := p1ol  
  | pv popol p1ol pinvol (invOL x1) := (pinvol _ (inductionOpB pv popol p1ol pinvol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpGroup1OL2Term2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpGroup1OL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 : (OpGroup1OL2Term2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpGroup1OL2Term2 n A)) , (P x))))))) 
  | pv2 psing2 popol2 p1ol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 p1ol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 p1ol2 pinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 p1ol2 pinvol2 x1) (inductionOp pv2 psing2 popol2 p1ol2 pinvol2 x2))  
  | pv2 psing2 popol2 p1ol2 pinvol2 oneOL2 := p1ol2  
  | pv2 psing2 popol2 p1ol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 popol2 p1ol2 pinvol2 x1))  
  def stageB  : (Group1LTerm → (Staged Group1LTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClGroup1ClTerm A) → (Staged (ClGroup1ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpGroup1OLTerm n) → (Staged (OpGroup1OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpGroup1OL2Term2 n A) → (Staged (OpGroup1OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (invT : ((Repr A) → (Repr A))) 
  
end Group1