import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Semigroup   
  structure Semigroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z)))) 
  
  open Semigroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Se1 : (Semigroup A1)) (Se2 : (Semigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Se1) x1 x2)) = ((op Se2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Se1 : (Semigroup A1)) (Se2 : (Semigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Se1) x1 x2) ((op Se2) y1 y2)))))) 
  
  inductive SemigroupTerm   : Type  
     | opL : (SemigroupTerm → (SemigroupTerm → SemigroupTerm))  
      open SemigroupTerm 
  
  inductive ClSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClSemigroupTerm) 
     | opCl : (ClSemigroupTerm → (ClSemigroupTerm → ClSemigroupTerm))  
      open ClSemigroupTerm 
  
  inductive OpSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSemigroupTerm) 
     | opOL : (OpSemigroupTerm → (OpSemigroupTerm → OpSemigroupTerm))  
      open OpSemigroupTerm 
  
  inductive OpSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSemigroupTerm2) 
     | sing2 : (A → OpSemigroupTerm2) 
     | opOL2 : (OpSemigroupTerm2 → (OpSemigroupTerm2 → OpSemigroupTerm2))  
      open OpSemigroupTerm2 
  
  def simplifyCl   {A : Type}  : ((ClSemigroupTerm A) → (ClSemigroupTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpSemigroupTerm n) → (OpSemigroupTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpSemigroupTerm2 n A) → (OpSemigroupTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Semigroup A) → (SemigroupTerm → A)) 
  | Se (opL x1 x2) := ((op Se) (evalB Se x1) (evalB Se x2))  
  def evalCl   {A : Type}  : ((Semigroup A) → ((ClSemigroupTerm A) → A)) 
  | Se (sing x1) := x1  
  | Se (opCl x1 x2) := ((op Se) (evalCl Se x1) (evalCl Se x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Semigroup A) → ((vector A n) → ((OpSemigroupTerm n) → A))) 
  | Se vars (v x1) := (nth vars x1)  
  | Se vars (opOL x1 x2) := ((op Se) (evalOpB Se vars x1) (evalOpB Se vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Semigroup A) → ((vector A n) → ((OpSemigroupTerm2 n A) → A))) 
  | Se vars (v2 x1) := (nth vars x1)  
  | Se vars (sing2 x1) := x1  
  | Se vars (opOL2 x1 x2) := ((op Se) (evalOp Se vars x1) (evalOp Se vars x2))  
  def inductionB   {P : (SemigroupTerm → Type)}  : ((∀ (x1 x2 : SemigroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : SemigroupTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClSemigroupTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClSemigroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClSemigroupTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpSemigroupTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpSemigroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpSemigroupTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpSemigroupTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpSemigroupTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (SemigroupTerm → (Staged SemigroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClSemigroupTerm A) → (Staged (ClSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpSemigroupTerm n) → (Staged (OpSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpSemigroupTerm2 n A) → (Staged (OpSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Semigroup