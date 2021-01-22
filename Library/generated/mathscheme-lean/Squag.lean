import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Squag   
  structure Squag  (A : Type) : Type := 
       (op : (A → (A → A)))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x)))
       (antiAbsorbent : (∀ {x y : A} , (op x (op x y)) = y))
       (idempotent_op : (∀ {x : A} , (op x x) = x)) 
  
  open Squag
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP)))
       (antiAbsorbentP : (∀ {xP yP : (Prod A A)} , (opP xP (opP xP yP)) = yP))
       (idempotent_opP : (∀ {xP : (Prod A A)} , (opP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Sq1 : (Squag A1)) (Sq2 : (Squag A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Sq1) x1 x2)) = ((op Sq2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Sq1 : (Squag A1)) (Sq2 : (Squag A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Sq1) x1 x2) ((op Sq2) y1 y2)))))) 
  
  inductive SquagTerm   : Type  
     | opL : (SquagTerm → (SquagTerm → SquagTerm))  
      open SquagTerm 
  
  inductive ClSquagTerm  (A : Type) : Type  
     | sing : (A → ClSquagTerm) 
     | opCl : (ClSquagTerm → (ClSquagTerm → ClSquagTerm))  
      open ClSquagTerm 
  
  inductive OpSquagTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSquagTerm) 
     | opOL : (OpSquagTerm → (OpSquagTerm → OpSquagTerm))  
      open OpSquagTerm 
  
  inductive OpSquagTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSquagTerm2) 
     | sing2 : (A → OpSquagTerm2) 
     | opOL2 : (OpSquagTerm2 → (OpSquagTerm2 → OpSquagTerm2))  
      open OpSquagTerm2 
  
  def simplifyCl   {A : Type}  : ((ClSquagTerm A) → (ClSquagTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpSquagTerm n) → (OpSquagTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpSquagTerm2 n A) → (OpSquagTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Squag A) → (SquagTerm → A)) 
  | Sq (opL x1 x2) := ((op Sq) (evalB Sq x1) (evalB Sq x2))  
  def evalCl   {A : Type}  : ((Squag A) → ((ClSquagTerm A) → A)) 
  | Sq (sing x1) := x1  
  | Sq (opCl x1 x2) := ((op Sq) (evalCl Sq x1) (evalCl Sq x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Squag A) → ((vector A n) → ((OpSquagTerm n) → A))) 
  | Sq vars (v x1) := (nth vars x1)  
  | Sq vars (opOL x1 x2) := ((op Sq) (evalOpB Sq vars x1) (evalOpB Sq vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Squag A) → ((vector A n) → ((OpSquagTerm2 n A) → A))) 
  | Sq vars (v2 x1) := (nth vars x1)  
  | Sq vars (sing2 x1) := x1  
  | Sq vars (opOL2 x1 x2) := ((op Sq) (evalOp Sq vars x1) (evalOp Sq vars x2))  
  def inductionB   {P : (SquagTerm → Type)}  : ((∀ (x1 x2 : SquagTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : SquagTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClSquagTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClSquagTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClSquagTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpSquagTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpSquagTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpSquagTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpSquagTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpSquagTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpSquagTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (SquagTerm → (Staged SquagTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClSquagTerm A) → (Staged (ClSquagTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpSquagTerm n) → (Staged (OpSquagTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpSquagTerm2 n A) → (Staged (OpSquagTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Squag