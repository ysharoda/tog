import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutivePointedSemigroup   
  structure InvolutivePointedSemigroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (prim : (A → A))
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x))
       (antidis_prim_op : (∀ {x y : A} , (prim (op x y)) = (op (prim y) (prim x)))) 
  
  open InvolutivePointedSemigroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS)
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (primP : ((Prod A A) → (Prod A A)))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP))
       (antidis_prim_opP : (∀ {xP yP : (Prod A A)} , (primP (opP xP yP)) = (opP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutivePointedSemigroup A1)) (In2 : (InvolutivePointedSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op In1) x1 x2)) = ((op In2) (hom x1) (hom x2))))
       (pres_e : (hom (e In1)) = (e In2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutivePointedSemigroup A1)) (In2 : (InvolutivePointedSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2))))))
       (interp_e : (interp (e In1) (e In2)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutivePointedSemigroupTerm   : Type  
     | opL : (InvolutivePointedSemigroupTerm → (InvolutivePointedSemigroupTerm → InvolutivePointedSemigroupTerm)) 
     | eL : InvolutivePointedSemigroupTerm 
     | primL : (InvolutivePointedSemigroupTerm → InvolutivePointedSemigroupTerm)  
      open InvolutivePointedSemigroupTerm 
  
  inductive ClInvolutivePointedSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClInvolutivePointedSemigroupTerm) 
     | opCl : (ClInvolutivePointedSemigroupTerm → (ClInvolutivePointedSemigroupTerm → ClInvolutivePointedSemigroupTerm)) 
     | eCl : ClInvolutivePointedSemigroupTerm 
     | primCl : (ClInvolutivePointedSemigroupTerm → ClInvolutivePointedSemigroupTerm)  
      open ClInvolutivePointedSemigroupTerm 
  
  inductive OpInvolutivePointedSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutivePointedSemigroupTerm) 
     | opOL : (OpInvolutivePointedSemigroupTerm → (OpInvolutivePointedSemigroupTerm → OpInvolutivePointedSemigroupTerm)) 
     | eOL : OpInvolutivePointedSemigroupTerm 
     | primOL : (OpInvolutivePointedSemigroupTerm → OpInvolutivePointedSemigroupTerm)  
      open OpInvolutivePointedSemigroupTerm 
  
  inductive OpInvolutivePointedSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutivePointedSemigroupTerm2) 
     | sing2 : (A → OpInvolutivePointedSemigroupTerm2) 
     | opOL2 : (OpInvolutivePointedSemigroupTerm2 → (OpInvolutivePointedSemigroupTerm2 → OpInvolutivePointedSemigroupTerm2)) 
     | eOL2 : OpInvolutivePointedSemigroupTerm2 
     | primOL2 : (OpInvolutivePointedSemigroupTerm2 → OpInvolutivePointedSemigroupTerm2)  
      open OpInvolutivePointedSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutivePointedSemigroupTerm A) → (ClInvolutivePointedSemigroupTerm A)) 
  | (primCl (primCl x)) := x  
  | (opCl (primCl y) (primCl x)) := (primCl (opCl x y))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutivePointedSemigroupTerm n) → (OpInvolutivePointedSemigroupTerm n)) 
  | (primOL (primOL x)) := x  
  | (opOL (primOL y) (primOL x)) := (primOL (opOL x y))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutivePointedSemigroupTerm2 n A) → (OpInvolutivePointedSemigroupTerm2 n A)) 
  | (primOL2 (primOL2 x)) := x  
  | (opOL2 (primOL2 y) (primOL2 x)) := (primOL2 (opOL2 x y))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutivePointedSemigroup A) → (InvolutivePointedSemigroupTerm → A)) 
  | In (opL x1 x2) := ((op In) (evalB In x1) (evalB In x2))  
  | In eL := (e In)  
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutivePointedSemigroup A) → ((ClInvolutivePointedSemigroupTerm A) → A)) 
  | In (sing x1) := x1  
  | In (opCl x1 x2) := ((op In) (evalCl In x1) (evalCl In x2))  
  | In eCl := (e In)  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutivePointedSemigroup A) → ((vector A n) → ((OpInvolutivePointedSemigroupTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (opOL x1 x2) := ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars eOL := (e In)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutivePointedSemigroup A) → ((vector A n) → ((OpInvolutivePointedSemigroupTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (opOL2 x1 x2) := ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars eOL2 := (e In)  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   (P : (InvolutivePointedSemigroupTerm → Type))  : ((∀ (x1 x2 : InvolutivePointedSemigroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ((∀ (x1 : InvolutivePointedSemigroupTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutivePointedSemigroupTerm) , (P x))))) 
  | popl pel ppriml (opL x1 x2) := (popl _ _ (inductionB popl pel ppriml x1) (inductionB popl pel ppriml x2))  
  | popl pel ppriml eL := pel  
  | popl pel ppriml (primL x1) := (ppriml _ (inductionB popl pel ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClInvolutivePointedSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClInvolutivePointedSemigroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ((∀ (x1 : (ClInvolutivePointedSemigroupTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutivePointedSemigroupTerm A)) , (P x)))))) 
  | psing popcl pecl pprimcl (sing x1) := (psing x1)  
  | psing popcl pecl pprimcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl pprimcl x1) (inductionCl psing popcl pecl pprimcl x2))  
  | psing popcl pecl pprimcl eCl := pecl  
  | psing popcl pecl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing popcl pecl pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutivePointedSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpInvolutivePointedSemigroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ((∀ (x1 : (OpInvolutivePointedSemigroupTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutivePointedSemigroupTerm n)) , (P x)))))) 
  | pv popol peol pprimol (v x1) := (pv x1)  
  | pv popol peol pprimol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol pprimol x1) (inductionOpB pv popol peol pprimol x2))  
  | pv popol peol pprimol eOL := peol  
  | pv popol peol pprimol (primOL x1) := (pprimol _ (inductionOpB pv popol peol pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutivePointedSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpInvolutivePointedSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ((∀ (x1 : (OpInvolutivePointedSemigroupTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutivePointedSemigroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 popol2 peol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 pprimol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 pprimol2 x1) (inductionOp pv2 psing2 popol2 peol2 pprimol2 x2))  
  | pv2 psing2 popol2 peol2 pprimol2 eOL2 := peol2  
  | pv2 psing2 popol2 peol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 popol2 peol2 pprimol2 x1))  
  def stageB  : (InvolutivePointedSemigroupTerm → (Staged InvolutivePointedSemigroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClInvolutivePointedSemigroupTerm A) → (Staged (ClInvolutivePointedSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpInvolutivePointedSemigroupTerm n) → (Staged (OpInvolutivePointedSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutivePointedSemigroupTerm2 n A) → (Staged (OpInvolutivePointedSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A))
       (primT : ((Repr A) → (Repr A))) 
  
end InvolutivePointedSemigroup