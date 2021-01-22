import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Involution   
  structure Involution  (A : Type) : Type := 
       (prim : (A → A))
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x)) 
  
  open Involution
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (Involution A1)) (In2 : (Involution A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (Involution A1)) (In2 : (Involution A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutionTerm   : Type  
     | primL : (InvolutionTerm → InvolutionTerm)  
      open InvolutionTerm 
  
  inductive ClInvolutionTerm  (A : Type) : Type  
     | sing : (A → ClInvolutionTerm) 
     | primCl : (ClInvolutionTerm → ClInvolutionTerm)  
      open ClInvolutionTerm 
  
  inductive OpInvolutionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutionTerm) 
     | primOL : (OpInvolutionTerm → OpInvolutionTerm)  
      open OpInvolutionTerm 
  
  inductive OpInvolutionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutionTerm2) 
     | sing2 : (A → OpInvolutionTerm2) 
     | primOL2 : (OpInvolutionTerm2 → OpInvolutionTerm2)  
      open OpInvolutionTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInvolutionTerm A) → (ClInvolutionTerm A)) 
  | (primCl (primCl x)) := x  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInvolutionTerm n) → (OpInvolutionTerm n)) 
  | (primOL (primOL x)) := x  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInvolutionTerm2 n A) → (OpInvolutionTerm2 n A)) 
  | (primOL2 (primOL2 x)) := x  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Involution A) → (InvolutionTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((Involution A) → ((ClInvolutionTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Involution A) → ((vector A n) → ((OpInvolutionTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((Involution A) → ((vector A n) → ((OpInvolutionTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   {P : (InvolutionTerm → Type)}  : ((∀ (x1 : InvolutionTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutionTerm) , (P x))) 
  | ppriml (primL x1) := (ppriml _ (inductionB ppriml x1))  
  def inductionCl   {A : Type} {P : ((ClInvolutionTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutionTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutionTerm A)) , (P x)))) 
  | psing pprimcl (sing x1) := (psing x1)  
  | psing pprimcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpInvolutionTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutionTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutionTerm n)) , (P x)))) 
  | pv pprimol (v x1) := (pv x1)  
  | pv pprimol (primOL x1) := (pprimol _ (inductionOpB pv pprimol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInvolutionTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutionTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutionTerm2 n A)) , (P x))))) 
  | pv2 psing2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 x1))  
  def stageB  : (InvolutionTerm → (Staged InvolutionTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClInvolutionTerm A) → (Staged (ClInvolutionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpInvolutionTerm n) → (Staged (OpInvolutionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInvolutionTerm2 n A) → (Staged (OpInvolutionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A))) 
  
end Involution