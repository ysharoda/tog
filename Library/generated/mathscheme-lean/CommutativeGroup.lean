import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CommutativeGroup   
  structure CommutativeGroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (runit_e : (∀ {x : A} , (op x e) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (inv : (A → A))
       (leftInverse_inv_op_e : (∀ {x : A} , (op x (inv x)) = e))
       (rightInverse_inv_op_e : (∀ {x : A} , (op (inv x) x) = e))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x))) 
  
  open CommutativeGroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS)
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (invP : ((Prod A A) → (Prod A A)))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (leftInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP xP (invP xP)) = eP))
       (rightInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP (invP xP) xP) = eP))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (CommutativeGroup A1)) (Co2 : (CommutativeGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Co1) x1 x2)) = ((op Co2) (hom x1) (hom x2))))
       (pres_e : (hom (e Co1)) = (e Co2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Co1) x1)) = ((inv Co2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (CommutativeGroup A1)) (Co2 : (CommutativeGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))))
       (interp_e : (interp (e Co1) (e Co2)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Co1) x1) ((inv Co2) y1))))) 
  
  inductive CommutativeGroupTerm   : Type  
     | opL : (CommutativeGroupTerm → (CommutativeGroupTerm → CommutativeGroupTerm)) 
     | eL : CommutativeGroupTerm 
     | invL : (CommutativeGroupTerm → CommutativeGroupTerm)  
      open CommutativeGroupTerm 
  
  inductive ClCommutativeGroupTerm  (A : Type) : Type  
     | sing : (A → ClCommutativeGroupTerm) 
     | opCl : (ClCommutativeGroupTerm → (ClCommutativeGroupTerm → ClCommutativeGroupTerm)) 
     | eCl : ClCommutativeGroupTerm 
     | invCl : (ClCommutativeGroupTerm → ClCommutativeGroupTerm)  
      open ClCommutativeGroupTerm 
  
  inductive OpCommutativeGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCommutativeGroupTerm) 
     | opOL : (OpCommutativeGroupTerm → (OpCommutativeGroupTerm → OpCommutativeGroupTerm)) 
     | eOL : OpCommutativeGroupTerm 
     | invOL : (OpCommutativeGroupTerm → OpCommutativeGroupTerm)  
      open OpCommutativeGroupTerm 
  
  inductive OpCommutativeGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCommutativeGroupTerm2) 
     | sing2 : (A → OpCommutativeGroupTerm2) 
     | opOL2 : (OpCommutativeGroupTerm2 → (OpCommutativeGroupTerm2 → OpCommutativeGroupTerm2)) 
     | eOL2 : OpCommutativeGroupTerm2 
     | invOL2 : (OpCommutativeGroupTerm2 → OpCommutativeGroupTerm2)  
      open OpCommutativeGroupTerm2 
  
  def simplifyCl   {A : Type}  : ((ClCommutativeGroupTerm A) → (ClCommutativeGroupTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x eCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpCommutativeGroupTerm n) → (OpCommutativeGroupTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x eOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpCommutativeGroupTerm2 n A) → (OpCommutativeGroupTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x eOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CommutativeGroup A) → (CommutativeGroupTerm → A)) 
  | Co (opL x1 x2) := ((op Co) (evalB Co x1) (evalB Co x2))  
  | Co eL := (e Co)  
  | Co (invL x1) := ((inv Co) (evalB Co x1))  
  def evalCl   {A : Type}  : ((CommutativeGroup A) → ((ClCommutativeGroupTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co (opCl x1 x2) := ((op Co) (evalCl Co x1) (evalCl Co x2))  
  | Co eCl := (e Co)  
  | Co (invCl x1) := ((inv Co) (evalCl Co x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((CommutativeGroup A) → ((vector A n) → ((OpCommutativeGroupTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars (opOL x1 x2) := ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  | Co vars eOL := (e Co)  
  | Co vars (invOL x1) := ((inv Co) (evalOpB Co vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((CommutativeGroup A) → ((vector A n) → ((OpCommutativeGroupTerm2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars (opOL2 x1 x2) := ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  | Co vars eOL2 := (e Co)  
  | Co vars (invOL2 x1) := ((inv Co) (evalOp Co vars x1))  
  def inductionB   {P : (CommutativeGroupTerm → Type)}  : ((∀ (x1 x2 : CommutativeGroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ((∀ (x1 : CommutativeGroupTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : CommutativeGroupTerm) , (P x))))) 
  | popl pel pinvl (opL x1 x2) := (popl _ _ (inductionB popl pel pinvl x1) (inductionB popl pel pinvl x2))  
  | popl pel pinvl eL := pel  
  | popl pel pinvl (invL x1) := (pinvl _ (inductionB popl pel pinvl x1))  
  def inductionCl   {A : Type} {P : ((ClCommutativeGroupTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCommutativeGroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ((∀ (x1 : (ClCommutativeGroupTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClCommutativeGroupTerm A)) , (P x)))))) 
  | psing popcl pecl pinvcl (sing x1) := (psing x1)  
  | psing popcl pecl pinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl pinvcl x1) (inductionCl psing popcl pecl pinvcl x2))  
  | psing popcl pecl pinvcl eCl := pecl  
  | psing popcl pecl pinvcl (invCl x1) := (pinvcl _ (inductionCl psing popcl pecl pinvcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpCommutativeGroupTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCommutativeGroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ((∀ (x1 : (OpCommutativeGroupTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpCommutativeGroupTerm n)) , (P x)))))) 
  | pv popol peol pinvol (v x1) := (pv x1)  
  | pv popol peol pinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol pinvol x1) (inductionOpB pv popol peol pinvol x2))  
  | pv popol peol pinvol eOL := peol  
  | pv popol peol pinvol (invOL x1) := (pinvol _ (inductionOpB pv popol peol pinvol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpCommutativeGroupTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCommutativeGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ((∀ (x1 : (OpCommutativeGroupTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpCommutativeGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 popol2 peol2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 pinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 pinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 pinvol2 x2))  
  | pv2 psing2 popol2 peol2 pinvol2 eOL2 := peol2  
  | pv2 psing2 popol2 peol2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 popol2 peol2 pinvol2 x1))  
  def stageB  : (CommutativeGroupTerm → (Staged CommutativeGroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClCommutativeGroupTerm A) → (Staged (ClCommutativeGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpCommutativeGroupTerm n) → (Staged (OpCommutativeGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpCommutativeGroupTerm2 n A) → (Staged (OpCommutativeGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A))
       (invT : ((Repr A) → (Repr A))) 
  
end CommutativeGroup