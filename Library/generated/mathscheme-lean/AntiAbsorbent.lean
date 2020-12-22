import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AntiAbsorbent   
  structure AntiAbsorbent  (A : Type) : Type := 
       (op : (A → (A → A)))
       (antiAbsorbent : (∀ {x y : A} , (op x (op x y)) = y)) 
  
  open AntiAbsorbent
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (antiAbsorbentP : (∀ {xP yP : (Prod A A)} , (opP xP (opP xP yP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (An1 : (AntiAbsorbent A1)) (An2 : (AntiAbsorbent A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op An1) x1 x2)) = ((op An2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (An1 : (AntiAbsorbent A1)) (An2 : (AntiAbsorbent A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op An1) x1 x2) ((op An2) y1 y2)))))) 
  
  inductive AntiAbsorbentTerm   : Type  
     | opL : (AntiAbsorbentTerm → (AntiAbsorbentTerm → AntiAbsorbentTerm))  
      open AntiAbsorbentTerm 
  
  inductive ClAntiAbsorbentTerm  (A : Type) : Type  
     | sing : (A → ClAntiAbsorbentTerm) 
     | opCl : (ClAntiAbsorbentTerm → (ClAntiAbsorbentTerm → ClAntiAbsorbentTerm))  
      open ClAntiAbsorbentTerm 
  
  inductive OpAntiAbsorbentTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAntiAbsorbentTerm) 
     | opOL : (OpAntiAbsorbentTerm → (OpAntiAbsorbentTerm → OpAntiAbsorbentTerm))  
      open OpAntiAbsorbentTerm 
  
  inductive OpAntiAbsorbentTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAntiAbsorbentTerm2) 
     | sing2 : (A → OpAntiAbsorbentTerm2) 
     | opOL2 : (OpAntiAbsorbentTerm2 → (OpAntiAbsorbentTerm2 → OpAntiAbsorbentTerm2))  
      open OpAntiAbsorbentTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAntiAbsorbentTerm A) → (ClAntiAbsorbentTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAntiAbsorbentTerm n) → (OpAntiAbsorbentTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAntiAbsorbentTerm2 n A) → (OpAntiAbsorbentTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AntiAbsorbent A) → (AntiAbsorbentTerm → A)) 
  | An (opL x1 x2) := ((op An) (evalB An x1) (evalB An x2))  
  def evalCl   {A : Type}  : ((AntiAbsorbent A) → ((ClAntiAbsorbentTerm A) → A)) 
  | An (sing x1) := x1  
  | An (opCl x1 x2) := ((op An) (evalCl An x1) (evalCl An x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AntiAbsorbent A) → ((vector A n) → ((OpAntiAbsorbentTerm n) → A))) 
  | An vars (v x1) := (nth vars x1)  
  | An vars (opOL x1 x2) := ((op An) (evalOpB An vars x1) (evalOpB An vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((AntiAbsorbent A) → ((vector A n) → ((OpAntiAbsorbentTerm2 n A) → A))) 
  | An vars (v2 x1) := (nth vars x1)  
  | An vars (sing2 x1) := x1  
  | An vars (opOL2 x1 x2) := ((op An) (evalOp An vars x1) (evalOp An vars x2))  
  def inductionB   (P : (AntiAbsorbentTerm → Type))  : ((∀ (x1 x2 : AntiAbsorbentTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : AntiAbsorbentTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClAntiAbsorbentTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAntiAbsorbentTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClAntiAbsorbentTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAntiAbsorbentTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAntiAbsorbentTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpAntiAbsorbentTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAntiAbsorbentTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAntiAbsorbentTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpAntiAbsorbentTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (AntiAbsorbentTerm → (Staged AntiAbsorbentTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAntiAbsorbentTerm A) → (Staged (ClAntiAbsorbentTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAntiAbsorbentTerm n) → (Staged (OpAntiAbsorbentTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAntiAbsorbentTerm2 n A) → (Staged (OpAntiAbsorbentTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AntiAbsorbent