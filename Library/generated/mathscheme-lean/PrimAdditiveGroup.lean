import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PrimAdditiveGroup   
  structure PrimAdditiveGroup  (A : Type) : Type := 
       (zero_ : A)
       (times_ : (A → (A → A)))
       (lunit_zero_ : (∀ {x : A} , (times_ zero_ x) = x))
       (runit_zero_ : (∀ {x : A} , (times_ x zero_) = x))
       (associative_times_ : (∀ {x y z : A} , (times_ (times_ x y) z) = (times_ x (times_ y z))))
       (inv_ : (A → A))
       (leftInverse_inv_op_zero_ : (∀ {x : A} , (times_ x (inv_ x)) = zero_))
       (rightInverse_inv_op_zero_ : (∀ {x : A} , (times_ (inv_ x) x) = zero_))
       (commutative_times_ : (∀ {x y : A} , (times_ x y) = (times_ y x))) 
  
  open PrimAdditiveGroup
  structure Sig  (AS : Type) : Type := 
       (zero_S : AS)
       (times_S : (AS → (AS → AS)))
       (inv_S : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (zero_P : (Prod A A))
       (times_P : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (inv_P : ((Prod A A) → (Prod A A)))
       (lunit_zero_P : (∀ {xP : (Prod A A)} , (times_P zero_P xP) = xP))
       (runit_zero_P : (∀ {xP : (Prod A A)} , (times_P xP zero_P) = xP))
       (associative_times_P : (∀ {xP yP zP : (Prod A A)} , (times_P (times_P xP yP) zP) = (times_P xP (times_P yP zP))))
       (leftInverse_inv_op_zero_P : (∀ {xP : (Prod A A)} , (times_P xP (inv_P xP)) = zero_P))
       (rightInverse_inv_op_zero_P : (∀ {xP : (Prod A A)} , (times_P (inv_P xP) xP) = zero_P))
       (commutative_times_P : (∀ {xP yP : (Prod A A)} , (times_P xP yP) = (times_P yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Pr1 : (PrimAdditiveGroup A1)) (Pr2 : (PrimAdditiveGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero_ : (hom (zero_ Pr1)) = (zero_ Pr2))
       (pres_times_ : (∀ {x1 x2 : A1} , (hom ((times_ Pr1) x1 x2)) = ((times_ Pr2) (hom x1) (hom x2))))
       (pres_inv_ : (∀ {x1 : A1} , (hom ((inv_ Pr1) x1)) = ((inv_ Pr2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Pr1 : (PrimAdditiveGroup A1)) (Pr2 : (PrimAdditiveGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero_ : (interp (zero_ Pr1) (zero_ Pr2)))
       (interp_times_ : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times_ Pr1) x1 x2) ((times_ Pr2) y1 y2))))))
       (interp_inv_ : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv_ Pr1) x1) ((inv_ Pr2) y1))))) 
  
  inductive PrimAdditiveGroupTerm   : Type  
     | zero_L : PrimAdditiveGroupTerm 
     | times_L : (PrimAdditiveGroupTerm → (PrimAdditiveGroupTerm → PrimAdditiveGroupTerm)) 
     | inv_L : (PrimAdditiveGroupTerm → PrimAdditiveGroupTerm)  
      open PrimAdditiveGroupTerm 
  
  inductive ClPrimAdditiveGroupTerm  (A : Type) : Type  
     | sing : (A → ClPrimAdditiveGroupTerm) 
     | zero_Cl : ClPrimAdditiveGroupTerm 
     | times_Cl : (ClPrimAdditiveGroupTerm → (ClPrimAdditiveGroupTerm → ClPrimAdditiveGroupTerm)) 
     | inv_Cl : (ClPrimAdditiveGroupTerm → ClPrimAdditiveGroupTerm)  
      open ClPrimAdditiveGroupTerm 
  
  inductive OpPrimAdditiveGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPrimAdditiveGroupTerm) 
     | zero_OL : OpPrimAdditiveGroupTerm 
     | times_OL : (OpPrimAdditiveGroupTerm → (OpPrimAdditiveGroupTerm → OpPrimAdditiveGroupTerm)) 
     | inv_OL : (OpPrimAdditiveGroupTerm → OpPrimAdditiveGroupTerm)  
      open OpPrimAdditiveGroupTerm 
  
  inductive OpPrimAdditiveGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPrimAdditiveGroupTerm2) 
     | sing2 : (A → OpPrimAdditiveGroupTerm2) 
     | zero_OL2 : OpPrimAdditiveGroupTerm2 
     | times_OL2 : (OpPrimAdditiveGroupTerm2 → (OpPrimAdditiveGroupTerm2 → OpPrimAdditiveGroupTerm2)) 
     | inv_OL2 : (OpPrimAdditiveGroupTerm2 → OpPrimAdditiveGroupTerm2)  
      open OpPrimAdditiveGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPrimAdditiveGroupTerm A) → (ClPrimAdditiveGroupTerm A)) 
  | (times_Cl zero_Cl x) := x  
  | (times_Cl x zero_Cl) := x  
  | zero_Cl := zero_Cl  
  | (times_Cl x1 x2) := (times_Cl (simplifyCl x1) (simplifyCl x2))  
  | (inv_Cl x1) := (inv_Cl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPrimAdditiveGroupTerm n) → (OpPrimAdditiveGroupTerm n)) 
  | (times_OL zero_OL x) := x  
  | (times_OL x zero_OL) := x  
  | zero_OL := zero_OL  
  | (times_OL x1 x2) := (times_OL (simplifyOpB x1) (simplifyOpB x2))  
  | (inv_OL x1) := (inv_OL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPrimAdditiveGroupTerm2 n A) → (OpPrimAdditiveGroupTerm2 n A)) 
  | (times_OL2 zero_OL2 x) := x  
  | (times_OL2 x zero_OL2) := x  
  | zero_OL2 := zero_OL2  
  | (times_OL2 x1 x2) := (times_OL2 (simplifyOp x1) (simplifyOp x2))  
  | (inv_OL2 x1) := (inv_OL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PrimAdditiveGroup A) → (PrimAdditiveGroupTerm → A)) 
  | Pr zero_L := (zero_ Pr)  
  | Pr (times_L x1 x2) := ((times_ Pr) (evalB Pr x1) (evalB Pr x2))  
  | Pr (inv_L x1) := ((inv_ Pr) (evalB Pr x1))  
  def evalCl   {A : Type}  : ((PrimAdditiveGroup A) → ((ClPrimAdditiveGroupTerm A) → A)) 
  | Pr (sing x1) := x1  
  | Pr zero_Cl := (zero_ Pr)  
  | Pr (times_Cl x1 x2) := ((times_ Pr) (evalCl Pr x1) (evalCl Pr x2))  
  | Pr (inv_Cl x1) := ((inv_ Pr) (evalCl Pr x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((PrimAdditiveGroup A) → ((vector A n) → ((OpPrimAdditiveGroupTerm n) → A))) 
  | Pr vars (v x1) := (nth vars x1)  
  | Pr vars zero_OL := (zero_ Pr)  
  | Pr vars (times_OL x1 x2) := ((times_ Pr) (evalOpB Pr vars x1) (evalOpB Pr vars x2))  
  | Pr vars (inv_OL x1) := ((inv_ Pr) (evalOpB Pr vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((PrimAdditiveGroup A) → ((vector A n) → ((OpPrimAdditiveGroupTerm2 n A) → A))) 
  | Pr vars (v2 x1) := (nth vars x1)  
  | Pr vars (sing2 x1) := x1  
  | Pr vars zero_OL2 := (zero_ Pr)  
  | Pr vars (times_OL2 x1 x2) := ((times_ Pr) (evalOp Pr vars x1) (evalOp Pr vars x2))  
  | Pr vars (inv_OL2 x1) := ((inv_ Pr) (evalOp Pr vars x1))  
  def inductionB   (P : (PrimAdditiveGroupTerm → Type))  : ((P zero_L) → ((∀ (x1 x2 : PrimAdditiveGroupTerm) , ((P x1) → ((P x2) → (P (times_L x1 x2))))) → ((∀ (x1 : PrimAdditiveGroupTerm) , ((P x1) → (P (inv_L x1)))) → (∀ (x : PrimAdditiveGroupTerm) , (P x))))) 
  | p0_l ptimes_l pinv_l zero_L := p0_l  
  | p0_l ptimes_l pinv_l (times_L x1 x2) := (ptimes_l _ _ (inductionB p0_l ptimes_l pinv_l x1) (inductionB p0_l ptimes_l pinv_l x2))  
  | p0_l ptimes_l pinv_l (inv_L x1) := (pinv_l _ (inductionB p0_l ptimes_l pinv_l x1))  
  def inductionCl   (A : Type) (P : ((ClPrimAdditiveGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zero_Cl) → ((∀ (x1 x2 : (ClPrimAdditiveGroupTerm A)) , ((P x1) → ((P x2) → (P (times_Cl x1 x2))))) → ((∀ (x1 : (ClPrimAdditiveGroupTerm A)) , ((P x1) → (P (inv_Cl x1)))) → (∀ (x : (ClPrimAdditiveGroupTerm A)) , (P x)))))) 
  | psing p0_cl ptimes_cl pinv_cl (sing x1) := (psing x1)  
  | psing p0_cl ptimes_cl pinv_cl zero_Cl := p0_cl  
  | psing p0_cl ptimes_cl pinv_cl (times_Cl x1 x2) := (ptimes_cl _ _ (inductionCl psing p0_cl ptimes_cl pinv_cl x1) (inductionCl psing p0_cl ptimes_cl pinv_cl x2))  
  | psing p0_cl ptimes_cl pinv_cl (inv_Cl x1) := (pinv_cl _ (inductionCl psing p0_cl ptimes_cl pinv_cl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpPrimAdditiveGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zero_OL) → ((∀ (x1 x2 : (OpPrimAdditiveGroupTerm n)) , ((P x1) → ((P x2) → (P (times_OL x1 x2))))) → ((∀ (x1 : (OpPrimAdditiveGroupTerm n)) , ((P x1) → (P (inv_OL x1)))) → (∀ (x : (OpPrimAdditiveGroupTerm n)) , (P x)))))) 
  | pv p0_ol ptimes_ol pinv_ol (v x1) := (pv x1)  
  | pv p0_ol ptimes_ol pinv_ol zero_OL := p0_ol  
  | pv p0_ol ptimes_ol pinv_ol (times_OL x1 x2) := (ptimes_ol _ _ (inductionOpB pv p0_ol ptimes_ol pinv_ol x1) (inductionOpB pv p0_ol ptimes_ol pinv_ol x2))  
  | pv p0_ol ptimes_ol pinv_ol (inv_OL x1) := (pinv_ol _ (inductionOpB pv p0_ol ptimes_ol pinv_ol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPrimAdditiveGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zero_OL2) → ((∀ (x1 x2 : (OpPrimAdditiveGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (times_OL2 x1 x2))))) → ((∀ (x1 : (OpPrimAdditiveGroupTerm2 n A)) , ((P x1) → (P (inv_OL2 x1)))) → (∀ (x : (OpPrimAdditiveGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 zero_OL2 := p0_ol2  
  | pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 (times_OL2 x1 x2) := (ptimes_ol2 _ _ (inductionOp pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 x1) (inductionOp pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 x2))  
  | pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 (inv_OL2 x1) := (pinv_ol2 _ (inductionOp pv2 psing2 p0_ol2 ptimes_ol2 pinv_ol2 x1))  
  def stageB  : (PrimAdditiveGroupTerm → (Staged PrimAdditiveGroupTerm))
  | zero_L := (Now zero_L)  
  | (times_L x1 x2) := (stage2 times_L (codeLift2 times_L) (stageB x1) (stageB x2))  
  | (inv_L x1) := (stage1 inv_L (codeLift1 inv_L) (stageB x1))  
  def stageCl   (A : Type)  : ((ClPrimAdditiveGroupTerm A) → (Staged (ClPrimAdditiveGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zero_Cl := (Now zero_Cl)  
  | (times_Cl x1 x2) := (stage2 times_Cl (codeLift2 times_Cl) (stageCl x1) (stageCl x2))  
  | (inv_Cl x1) := (stage1 inv_Cl (codeLift1 inv_Cl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpPrimAdditiveGroupTerm n) → (Staged (OpPrimAdditiveGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zero_OL := (Now zero_OL)  
  | (times_OL x1 x2) := (stage2 times_OL (codeLift2 times_OL) (stageOpB x1) (stageOpB x2))  
  | (inv_OL x1) := (stage1 inv_OL (codeLift1 inv_OL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPrimAdditiveGroupTerm2 n A) → (Staged (OpPrimAdditiveGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zero_OL2 := (Now zero_OL2)  
  | (times_OL2 x1 x2) := (stage2 times_OL2 (codeLift2 times_OL2) (stageOp x1) (stageOp x2))  
  | (inv_OL2 x1) := (stage1 inv_OL2 (codeLift1 inv_OL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zero_T : (Repr A))
       (times_T : ((Repr A) → ((Repr A) → (Repr A))))
       (inv_T : ((Repr A) → (Repr A))) 
  
end PrimAdditiveGroup