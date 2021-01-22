import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MeetSemilattice   
  structure MeetSemilattice  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (idempotent_op : (∀ {x : A} , (op x x) = x))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x))) 
  
  open MeetSemilattice
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (idempotent_opP : (∀ {xP : (Prod A A)} , (opP xP xP) = xP))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Me1 : (MeetSemilattice A1)) (Me2 : (MeetSemilattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Me1) x1 x2)) = ((op Me2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Me1 : (MeetSemilattice A1)) (Me2 : (MeetSemilattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Me1) x1 x2) ((op Me2) y1 y2)))))) 
  
  inductive MeetSemilatticeTerm   : Type  
     | opL : (MeetSemilatticeTerm → (MeetSemilatticeTerm → MeetSemilatticeTerm))  
      open MeetSemilatticeTerm 
  
  inductive ClMeetSemilatticeTerm  (A : Type) : Type  
     | sing : (A → ClMeetSemilatticeTerm) 
     | opCl : (ClMeetSemilatticeTerm → (ClMeetSemilatticeTerm → ClMeetSemilatticeTerm))  
      open ClMeetSemilatticeTerm 
  
  inductive OpMeetSemilatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMeetSemilatticeTerm) 
     | opOL : (OpMeetSemilatticeTerm → (OpMeetSemilatticeTerm → OpMeetSemilatticeTerm))  
      open OpMeetSemilatticeTerm 
  
  inductive OpMeetSemilatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMeetSemilatticeTerm2) 
     | sing2 : (A → OpMeetSemilatticeTerm2) 
     | opOL2 : (OpMeetSemilatticeTerm2 → (OpMeetSemilatticeTerm2 → OpMeetSemilatticeTerm2))  
      open OpMeetSemilatticeTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMeetSemilatticeTerm A) → (ClMeetSemilatticeTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMeetSemilatticeTerm n) → (OpMeetSemilatticeTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMeetSemilatticeTerm2 n A) → (OpMeetSemilatticeTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MeetSemilattice A) → (MeetSemilatticeTerm → A)) 
  | Me (opL x1 x2) := ((op Me) (evalB Me x1) (evalB Me x2))  
  def evalCl   {A : Type}  : ((MeetSemilattice A) → ((ClMeetSemilatticeTerm A) → A)) 
  | Me (sing x1) := x1  
  | Me (opCl x1 x2) := ((op Me) (evalCl Me x1) (evalCl Me x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((MeetSemilattice A) → ((vector A n) → ((OpMeetSemilatticeTerm n) → A))) 
  | Me vars (v x1) := (nth vars x1)  
  | Me vars (opOL x1 x2) := ((op Me) (evalOpB Me vars x1) (evalOpB Me vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((MeetSemilattice A) → ((vector A n) → ((OpMeetSemilatticeTerm2 n A) → A))) 
  | Me vars (v2 x1) := (nth vars x1)  
  | Me vars (sing2 x1) := x1  
  | Me vars (opOL2 x1 x2) := ((op Me) (evalOp Me vars x1) (evalOp Me vars x2))  
  def inductionB   {P : (MeetSemilatticeTerm → Type)}  : ((∀ (x1 x2 : MeetSemilatticeTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : MeetSemilatticeTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClMeetSemilatticeTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMeetSemilatticeTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClMeetSemilatticeTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMeetSemilatticeTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMeetSemilatticeTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpMeetSemilatticeTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMeetSemilatticeTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMeetSemilatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpMeetSemilatticeTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (MeetSemilatticeTerm → (Staged MeetSemilatticeTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMeetSemilatticeTerm A) → (Staged (ClMeetSemilatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMeetSemilatticeTerm n) → (Staged (OpMeetSemilatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMeetSemilatticeTerm2 n A) → (Staged (OpMeetSemilatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MeetSemilattice