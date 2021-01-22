import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Monoid1   
  structure Monoid1  (A : Type) : Type := 
       (one : A)
       (op : (A → (A → A)))
       (lunit_one : (∀ {x : A} , (op one x) = x))
       (runit_one : (∀ {x : A} , (op x one) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z)))) 
  
  open Monoid1
  structure Sig  (AS : Type) : Type := 
       (oneS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (opP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (opP xP oneP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mo1 : (Monoid1 A1)) (Mo2 : (Monoid1 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one Mo1)) = (one Mo2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Mo1) x1 x2)) = ((op Mo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mo1 : (Monoid1 A1)) (Mo2 : (Monoid1 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one Mo1) (one Mo2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2)))))) 
  
  inductive Monoid1LTerm   : Type  
     | oneL : Monoid1LTerm 
     | opL : (Monoid1LTerm → (Monoid1LTerm → Monoid1LTerm))  
      open Monoid1LTerm 
  
  inductive ClMonoid1ClTerm  (A : Type) : Type  
     | sing : (A → ClMonoid1ClTerm) 
     | oneCl : ClMonoid1ClTerm 
     | opCl : (ClMonoid1ClTerm → (ClMonoid1ClTerm → ClMonoid1ClTerm))  
      open ClMonoid1ClTerm 
  
  inductive OpMonoid1OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMonoid1OLTerm) 
     | oneOL : OpMonoid1OLTerm 
     | opOL : (OpMonoid1OLTerm → (OpMonoid1OLTerm → OpMonoid1OLTerm))  
      open OpMonoid1OLTerm 
  
  inductive OpMonoid1OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMonoid1OL2Term2) 
     | sing2 : (A → OpMonoid1OL2Term2) 
     | oneOL2 : OpMonoid1OL2Term2 
     | opOL2 : (OpMonoid1OL2Term2 → (OpMonoid1OL2Term2 → OpMonoid1OL2Term2))  
      open OpMonoid1OL2Term2 
  
  def simplifyCl   {A : Type}  : ((ClMonoid1ClTerm A) → (ClMonoid1ClTerm A)) 
  | (opCl oneCl x) := x  
  | (opCl x oneCl) := x  
  | oneCl := oneCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMonoid1OLTerm n) → (OpMonoid1OLTerm n)) 
  | (opOL oneOL x) := x  
  | (opOL x oneOL) := x  
  | oneOL := oneOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMonoid1OL2Term2 n A) → (OpMonoid1OL2Term2 n A)) 
  | (opOL2 oneOL2 x) := x  
  | (opOL2 x oneOL2) := x  
  | oneOL2 := oneOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Monoid1 A) → (Monoid1LTerm → A)) 
  | Mo oneL := (one Mo)  
  | Mo (opL x1 x2) := ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  def evalCl   {A : Type}  : ((Monoid1 A) → ((ClMonoid1ClTerm A) → A)) 
  | Mo (sing x1) := x1  
  | Mo oneCl := (one Mo)  
  | Mo (opCl x1 x2) := ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Monoid1 A) → ((vector A n) → ((OpMonoid1OLTerm n) → A))) 
  | Mo vars (v x1) := (nth vars x1)  
  | Mo vars oneOL := (one Mo)  
  | Mo vars (opOL x1 x2) := ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Monoid1 A) → ((vector A n) → ((OpMonoid1OL2Term2 n A) → A))) 
  | Mo vars (v2 x1) := (nth vars x1)  
  | Mo vars (sing2 x1) := x1  
  | Mo vars oneOL2 := (one Mo)  
  | Mo vars (opOL2 x1 x2) := ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  def inductionB   {P : (Monoid1LTerm → Type)}  : ((P oneL) → ((∀ (x1 x2 : Monoid1LTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : Monoid1LTerm) , (P x)))) 
  | p1l popl oneL := p1l  
  | p1l popl (opL x1 x2) := (popl _ _ (inductionB p1l popl x1) (inductionB p1l popl x2))  
  def inductionCl   {A : Type} {P : ((ClMonoid1ClTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → ((∀ (x1 x2 : (ClMonoid1ClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClMonoid1ClTerm A)) , (P x))))) 
  | psing p1cl popcl (sing x1) := (psing x1)  
  | psing p1cl popcl oneCl := p1cl  
  | psing p1cl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing p1cl popcl x1) (inductionCl psing p1cl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMonoid1OLTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → ((∀ (x1 x2 : (OpMonoid1OLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpMonoid1OLTerm n)) , (P x))))) 
  | pv p1ol popol (v x1) := (pv x1)  
  | pv p1ol popol oneOL := p1ol  
  | pv p1ol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv p1ol popol x1) (inductionOpB pv p1ol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMonoid1OL2Term2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → ((∀ (x1 x2 : (OpMonoid1OL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpMonoid1OL2Term2 n A)) , (P x)))))) 
  | pv2 psing2 p1ol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 popol2 oneOL2 := p1ol2  
  | pv2 psing2 p1ol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 p1ol2 popol2 x1) (inductionOp pv2 psing2 p1ol2 popol2 x2))  
  def stageB  : (Monoid1LTerm → (Staged Monoid1LTerm))
  | oneL := (Now oneL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMonoid1ClTerm A) → (Staged (ClMonoid1ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMonoid1OLTerm n) → (Staged (OpMonoid1OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMonoid1OL2Term2 n A) → (Staged (OpMonoid1OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Monoid1