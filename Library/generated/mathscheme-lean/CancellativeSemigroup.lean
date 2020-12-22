import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CancellativeSemigroup   
  structure CancellativeSemigroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (leftCancellative : (∀ {x y z : A} , ((op z x) = (op z y) → x = y)))
       (rightCancellative : (∀ {x y z : A} , ((op x z) = (op y z) → x = y))) 
  
  open CancellativeSemigroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (leftCancellativeP : (∀ {xP yP zP : (Prod A A)} , ((opP zP xP) = (opP zP yP) → xP = yP)))
       (rightCancellativeP : (∀ {xP yP zP : (Prod A A)} , ((opP xP zP) = (opP yP zP) → xP = yP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ca1 : (CancellativeSemigroup A1)) (Ca2 : (CancellativeSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ca1) x1 x2)) = ((op Ca2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ca1 : (CancellativeSemigroup A1)) (Ca2 : (CancellativeSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ca1) x1 x2) ((op Ca2) y1 y2)))))) 
  
  inductive CancellativeSemigroupTerm   : Type  
     | opL : (CancellativeSemigroupTerm → (CancellativeSemigroupTerm → CancellativeSemigroupTerm))  
      open CancellativeSemigroupTerm 
  
  inductive ClCancellativeSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClCancellativeSemigroupTerm) 
     | opCl : (ClCancellativeSemigroupTerm → (ClCancellativeSemigroupTerm → ClCancellativeSemigroupTerm))  
      open ClCancellativeSemigroupTerm 
  
  inductive OpCancellativeSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCancellativeSemigroupTerm) 
     | opOL : (OpCancellativeSemigroupTerm → (OpCancellativeSemigroupTerm → OpCancellativeSemigroupTerm))  
      open OpCancellativeSemigroupTerm 
  
  inductive OpCancellativeSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCancellativeSemigroupTerm2) 
     | sing2 : (A → OpCancellativeSemigroupTerm2) 
     | opOL2 : (OpCancellativeSemigroupTerm2 → (OpCancellativeSemigroupTerm2 → OpCancellativeSemigroupTerm2))  
      open OpCancellativeSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClCancellativeSemigroupTerm A) → (ClCancellativeSemigroupTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpCancellativeSemigroupTerm n) → (OpCancellativeSemigroupTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpCancellativeSemigroupTerm2 n A) → (OpCancellativeSemigroupTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CancellativeSemigroup A) → (CancellativeSemigroupTerm → A)) 
  | Ca (opL x1 x2) := ((op Ca) (evalB Ca x1) (evalB Ca x2))  
  def evalCl   {A : Type}  : ((CancellativeSemigroup A) → ((ClCancellativeSemigroupTerm A) → A)) 
  | Ca (sing x1) := x1  
  | Ca (opCl x1 x2) := ((op Ca) (evalCl Ca x1) (evalCl Ca x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((CancellativeSemigroup A) → ((vector A n) → ((OpCancellativeSemigroupTerm n) → A))) 
  | Ca vars (v x1) := (nth vars x1)  
  | Ca vars (opOL x1 x2) := ((op Ca) (evalOpB Ca vars x1) (evalOpB Ca vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((CancellativeSemigroup A) → ((vector A n) → ((OpCancellativeSemigroupTerm2 n A) → A))) 
  | Ca vars (v2 x1) := (nth vars x1)  
  | Ca vars (sing2 x1) := x1  
  | Ca vars (opOL2 x1 x2) := ((op Ca) (evalOp Ca vars x1) (evalOp Ca vars x2))  
  def inductionB   (P : (CancellativeSemigroupTerm → Type))  : ((∀ (x1 x2 : CancellativeSemigroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : CancellativeSemigroupTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClCancellativeSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCancellativeSemigroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClCancellativeSemigroupTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpCancellativeSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCancellativeSemigroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpCancellativeSemigroupTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpCancellativeSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCancellativeSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpCancellativeSemigroupTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (CancellativeSemigroupTerm → (Staged CancellativeSemigroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClCancellativeSemigroupTerm A) → (Staged (ClCancellativeSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpCancellativeSemigroupTerm n) → (Staged (OpCancellativeSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpCancellativeSemigroupTerm2 n A) → (Staged (OpCancellativeSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end CancellativeSemigroup