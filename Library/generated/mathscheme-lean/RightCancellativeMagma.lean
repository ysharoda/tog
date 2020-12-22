import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightCancellativeMagma   
  structure RightCancellativeMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (rightCancellative : (∀ {x y z : A} , ((op x z) = (op y z) → x = y))) 
  
  open RightCancellativeMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightCancellativeP : (∀ {xP yP zP : (Prod A A)} , ((opP xP zP) = (opP yP zP) → xP = yP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightCancellativeMagma A1)) (Ri2 : (RightCancellativeMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ri1) x1 x2)) = ((op Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightCancellativeMagma A1)) (Ri2 : (RightCancellativeMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))) 
  
  inductive RightCancellativeMagmaTerm   : Type  
     | opL : (RightCancellativeMagmaTerm → (RightCancellativeMagmaTerm → RightCancellativeMagmaTerm))  
      open RightCancellativeMagmaTerm 
  
  inductive ClRightCancellativeMagmaTerm  (A : Type) : Type  
     | sing : (A → ClRightCancellativeMagmaTerm) 
     | opCl : (ClRightCancellativeMagmaTerm → (ClRightCancellativeMagmaTerm → ClRightCancellativeMagmaTerm))  
      open ClRightCancellativeMagmaTerm 
  
  inductive OpRightCancellativeMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightCancellativeMagmaTerm) 
     | opOL : (OpRightCancellativeMagmaTerm → (OpRightCancellativeMagmaTerm → OpRightCancellativeMagmaTerm))  
      open OpRightCancellativeMagmaTerm 
  
  inductive OpRightCancellativeMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightCancellativeMagmaTerm2) 
     | sing2 : (A → OpRightCancellativeMagmaTerm2) 
     | opOL2 : (OpRightCancellativeMagmaTerm2 → (OpRightCancellativeMagmaTerm2 → OpRightCancellativeMagmaTerm2))  
      open OpRightCancellativeMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRightCancellativeMagmaTerm A) → (ClRightCancellativeMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRightCancellativeMagmaTerm n) → (OpRightCancellativeMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRightCancellativeMagmaTerm2 n A) → (OpRightCancellativeMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightCancellativeMagma A) → (RightCancellativeMagmaTerm → A)) 
  | Ri (opL x1 x2) := ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightCancellativeMagma A) → ((ClRightCancellativeMagmaTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (opCl x1 x2) := ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((RightCancellativeMagma A) → ((vector A n) → ((OpRightCancellativeMagmaTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (opOL x1 x2) := ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((RightCancellativeMagma A) → ((vector A n) → ((OpRightCancellativeMagmaTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (opOL2 x1 x2) := ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   (P : (RightCancellativeMagmaTerm → Type))  : ((∀ (x1 x2 : RightCancellativeMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : RightCancellativeMagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClRightCancellativeMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightCancellativeMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClRightCancellativeMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpRightCancellativeMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightCancellativeMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpRightCancellativeMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRightCancellativeMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightCancellativeMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpRightCancellativeMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (RightCancellativeMagmaTerm → (Staged RightCancellativeMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClRightCancellativeMagmaTerm A) → (Staged (ClRightCancellativeMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpRightCancellativeMagmaTerm n) → (Staged (OpRightCancellativeMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRightCancellativeMagmaTerm2 n A) → (Staged (OpRightCancellativeMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightCancellativeMagma