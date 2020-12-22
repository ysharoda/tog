import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CommutativeMonoid1   
  structure CommutativeMonoid1  (A : Type) : Type := 
       (op : (A → (A → A)))
       (one : A)
       (lunit_one : (∀ {x : A} , (op one x) = x))
       (runit_one : (∀ {x : A} , (op x one) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x))) 
  
  open CommutativeMonoid1
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (lunit_1P : (∀ {xP : (Prod A A)} , (opP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (opP xP oneP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (CommutativeMonoid1 A1)) (Co2 : (CommutativeMonoid1 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Co1) x1 x2)) = ((op Co2) (hom x1) (hom x2))))
       (pres_one : (hom (one Co1)) = (one Co2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (CommutativeMonoid1 A1)) (Co2 : (CommutativeMonoid1 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))))
       (interp_one : (interp (one Co1) (one Co2))) 
  
  inductive CommutativeMonoid1LTerm   : Type  
     | opL : (CommutativeMonoid1LTerm → (CommutativeMonoid1LTerm → CommutativeMonoid1LTerm)) 
     | oneL : CommutativeMonoid1LTerm  
      open CommutativeMonoid1LTerm 
  
  inductive ClCommutativeMonoid1ClTerm  (A : Type) : Type  
     | sing : (A → ClCommutativeMonoid1ClTerm) 
     | opCl : (ClCommutativeMonoid1ClTerm → (ClCommutativeMonoid1ClTerm → ClCommutativeMonoid1ClTerm)) 
     | oneCl : ClCommutativeMonoid1ClTerm  
      open ClCommutativeMonoid1ClTerm 
  
  inductive OpCommutativeMonoid1OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCommutativeMonoid1OLTerm) 
     | opOL : (OpCommutativeMonoid1OLTerm → (OpCommutativeMonoid1OLTerm → OpCommutativeMonoid1OLTerm)) 
     | oneOL : OpCommutativeMonoid1OLTerm  
      open OpCommutativeMonoid1OLTerm 
  
  inductive OpCommutativeMonoid1OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCommutativeMonoid1OL2Term2) 
     | sing2 : (A → OpCommutativeMonoid1OL2Term2) 
     | opOL2 : (OpCommutativeMonoid1OL2Term2 → (OpCommutativeMonoid1OL2Term2 → OpCommutativeMonoid1OL2Term2)) 
     | oneOL2 : OpCommutativeMonoid1OL2Term2  
      open OpCommutativeMonoid1OL2Term2 
  
  def simplifyCl   (A : Type)  : ((ClCommutativeMonoid1ClTerm A) → (ClCommutativeMonoid1ClTerm A)) 
  | (opCl oneCl x) := x  
  | (opCl x oneCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpCommutativeMonoid1OLTerm n) → (OpCommutativeMonoid1OLTerm n)) 
  | (opOL oneOL x) := x  
  | (opOL x oneOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpCommutativeMonoid1OL2Term2 n A) → (OpCommutativeMonoid1OL2Term2 n A)) 
  | (opOL2 oneOL2 x) := x  
  | (opOL2 x oneOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CommutativeMonoid1 A) → (CommutativeMonoid1LTerm → A)) 
  | Co (opL x1 x2) := ((op Co) (evalB Co x1) (evalB Co x2))  
  | Co oneL := (one Co)  
  def evalCl   {A : Type}  : ((CommutativeMonoid1 A) → ((ClCommutativeMonoid1ClTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co (opCl x1 x2) := ((op Co) (evalCl Co x1) (evalCl Co x2))  
  | Co oneCl := (one Co)  
  def evalOpB   {A : Type} (n : ℕ)  : ((CommutativeMonoid1 A) → ((vector A n) → ((OpCommutativeMonoid1OLTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars (opOL x1 x2) := ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  | Co vars oneOL := (one Co)  
  def evalOp   {A : Type} (n : ℕ)  : ((CommutativeMonoid1 A) → ((vector A n) → ((OpCommutativeMonoid1OL2Term2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars (opOL2 x1 x2) := ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  | Co vars oneOL2 := (one Co)  
  def inductionB   (P : (CommutativeMonoid1LTerm → Type))  : ((∀ (x1 x2 : CommutativeMonoid1LTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P oneL) → (∀ (x : CommutativeMonoid1LTerm) , (P x)))) 
  | popl p1l (opL x1 x2) := (popl _ _ (inductionB popl p1l x1) (inductionB popl p1l x2))  
  | popl p1l oneL := p1l  
  def inductionCl   (A : Type) (P : ((ClCommutativeMonoid1ClTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCommutativeMonoid1ClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P oneCl) → (∀ (x : (ClCommutativeMonoid1ClTerm A)) , (P x))))) 
  | psing popcl p1cl (sing x1) := (psing x1)  
  | psing popcl p1cl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl p1cl x1) (inductionCl psing popcl p1cl x2))  
  | psing popcl p1cl oneCl := p1cl  
  def inductionOpB   (n : ℕ) (P : ((OpCommutativeMonoid1OLTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCommutativeMonoid1OLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P oneOL) → (∀ (x : (OpCommutativeMonoid1OLTerm n)) , (P x))))) 
  | pv popol p1ol (v x1) := (pv x1)  
  | pv popol p1ol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol p1ol x1) (inductionOpB pv popol p1ol x2))  
  | pv popol p1ol oneOL := p1ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpCommutativeMonoid1OL2Term2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCommutativeMonoid1OL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P oneOL2) → (∀ (x : (OpCommutativeMonoid1OL2Term2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 p1ol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 p1ol2 x1) (inductionOp pv2 psing2 popol2 p1ol2 x2))  
  | pv2 psing2 popol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (CommutativeMonoid1LTerm → (Staged CommutativeMonoid1LTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  def stageCl   (A : Type)  : ((ClCommutativeMonoid1ClTerm A) → (Staged (ClCommutativeMonoid1ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  def stageOpB   (n : ℕ)  : ((OpCommutativeMonoid1OLTerm n) → (Staged (OpCommutativeMonoid1OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpCommutativeMonoid1OL2Term2 n A) → (Staged (OpCommutativeMonoid1OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A)) 
  
end CommutativeMonoid1