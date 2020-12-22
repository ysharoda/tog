import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveSemigroup   
  structure InvolutiveSemigroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (prim : (A → A))
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x))
       (antidis_prim_op : (∀ {x y : A} , (prim (op x y)) = (op (prim y) (prim x)))) 
  
  open InvolutiveSemigroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A)))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP))
       (antidis_prim_opP : (∀ {xP yP : (Prod A A)} , (primP (opP xP yP)) = (opP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveSemigroup A1)) (In2 : (InvolutiveSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op In1) x1 x2)) = ((op In2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveSemigroup A1)) (In2 : (InvolutiveSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutiveSemigroupTerm   : Type  
     | opL : (InvolutiveSemigroupTerm → (InvolutiveSemigroupTerm → InvolutiveSemigroupTerm)) 
     | primL : (InvolutiveSemigroupTerm → InvolutiveSemigroupTerm)  
      open InvolutiveSemigroupTerm 
  
  inductive ClInvolutiveSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveSemigroupTerm) 
     | opCl : (ClInvolutiveSemigroupTerm → (ClInvolutiveSemigroupTerm → ClInvolutiveSemigroupTerm)) 
     | primCl : (ClInvolutiveSemigroupTerm → ClInvolutiveSemigroupTerm)  
      open ClInvolutiveSemigroupTerm 
  
  inductive OpInvolutiveSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveSemigroupTerm) 
     | opOL : (OpInvolutiveSemigroupTerm → (OpInvolutiveSemigroupTerm → OpInvolutiveSemigroupTerm)) 
     | primOL : (OpInvolutiveSemigroupTerm → OpInvolutiveSemigroupTerm)  
      open OpInvolutiveSemigroupTerm 
  
  inductive OpInvolutiveSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveSemigroupTerm2) 
     | sing2 : (A → OpInvolutiveSemigroupTerm2) 
     | opOL2 : (OpInvolutiveSemigroupTerm2 → (OpInvolutiveSemigroupTerm2 → OpInvolutiveSemigroupTerm2)) 
     | primOL2 : (OpInvolutiveSemigroupTerm2 → OpInvolutiveSemigroupTerm2)  
      open OpInvolutiveSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutiveSemigroupTerm A) → (ClInvolutiveSemigroupTerm A)) 
  | (primCl (primCl x)) := x  
  | (opCl (primCl y) (primCl x)) := (primCl (opCl x y))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutiveSemigroupTerm n) → (OpInvolutiveSemigroupTerm n)) 
  | (primOL (primOL x)) := x  
  | (opOL (primOL y) (primOL x)) := (primOL (opOL x y))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutiveSemigroupTerm2 n A) → (OpInvolutiveSemigroupTerm2 n A)) 
  | (primOL2 (primOL2 x)) := x  
  | (opOL2 (primOL2 y) (primOL2 x)) := (primOL2 (opOL2 x y))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveSemigroup A) → (InvolutiveSemigroupTerm → A)) 
  | In (opL x1 x2) := ((op In) (evalB In x1) (evalB In x2))  
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutiveSemigroup A) → ((ClInvolutiveSemigroupTerm A) → A)) 
  | In (sing x1) := x1  
  | In (opCl x1 x2) := ((op In) (evalCl In x1) (evalCl In x2))  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutiveSemigroup A) → ((vector A n) → ((OpInvolutiveSemigroupTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (opOL x1 x2) := ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutiveSemigroup A) → ((vector A n) → ((OpInvolutiveSemigroupTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (opOL2 x1 x2) := ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   (P : (InvolutiveSemigroupTerm → Type))  : ((∀ (x1 x2 : InvolutiveSemigroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((∀ (x1 : InvolutiveSemigroupTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutiveSemigroupTerm) , (P x)))) 
  | popl ppriml (opL x1 x2) := (popl _ _ (inductionB popl ppriml x1) (inductionB popl ppriml x2))  
  | popl ppriml (primL x1) := (ppriml _ (inductionB popl ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClInvolutiveSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClInvolutiveSemigroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((∀ (x1 : (ClInvolutiveSemigroupTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutiveSemigroupTerm A)) , (P x))))) 
  | psing popcl pprimcl (sing x1) := (psing x1)  
  | psing popcl pprimcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pprimcl x1) (inductionCl psing popcl pprimcl x2))  
  | psing popcl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing popcl pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutiveSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpInvolutiveSemigroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((∀ (x1 : (OpInvolutiveSemigroupTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutiveSemigroupTerm n)) , (P x))))) 
  | pv popol pprimol (v x1) := (pv x1)  
  | pv popol pprimol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol pprimol x1) (inductionOpB pv popol pprimol x2))  
  | pv popol pprimol (primOL x1) := (pprimol _ (inductionOpB pv popol pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutiveSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpInvolutiveSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((∀ (x1 : (OpInvolutiveSemigroupTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutiveSemigroupTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 pprimol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 pprimol2 x1) (inductionOp pv2 psing2 popol2 pprimol2 x2))  
  | pv2 psing2 popol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 popol2 pprimol2 x1))  
  def stageB  : (InvolutiveSemigroupTerm → (Staged InvolutiveSemigroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClInvolutiveSemigroupTerm A) → (Staged (ClInvolutiveSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpInvolutiveSemigroupTerm n) → (Staged (OpInvolutiveSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutiveSemigroupTerm2 n A) → (Staged (OpInvolutiveSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end InvolutiveSemigroup