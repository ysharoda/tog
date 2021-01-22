import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InverseUnaryOperation   
  structure InverseUnaryOperation  (A : Type) : Type := 
       (inv : (A → A)) 
  
  open InverseUnaryOperation
  structure Sig  (AS : Type) : Type := 
       (invS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (invP : ((Prod A A) → (Prod A A))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InverseUnaryOperation A1)) (In2 : (InverseUnaryOperation A2)) : Type := 
       (hom : (A1 → A2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv In1) x1)) = ((inv In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InverseUnaryOperation A1)) (In2 : (InverseUnaryOperation A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv In1) x1) ((inv In2) y1))))) 
  
  inductive InverseUnaryOperationTerm   : Type  
     | invL : (InverseUnaryOperationTerm → InverseUnaryOperationTerm)  
      open InverseUnaryOperationTerm 
  
  inductive ClInverseUnaryOperationTerm  (A : Type) : Type  
     | sing : (A → ClInverseUnaryOperationTerm) 
     | invCl : (ClInverseUnaryOperationTerm → ClInverseUnaryOperationTerm)  
      open ClInverseUnaryOperationTerm 
  
  inductive OpInverseUnaryOperationTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInverseUnaryOperationTerm) 
     | invOL : (OpInverseUnaryOperationTerm → OpInverseUnaryOperationTerm)  
      open OpInverseUnaryOperationTerm 
  
  inductive OpInverseUnaryOperationTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInverseUnaryOperationTerm2) 
     | sing2 : (A → OpInverseUnaryOperationTerm2) 
     | invOL2 : (OpInverseUnaryOperationTerm2 → OpInverseUnaryOperationTerm2)  
      open OpInverseUnaryOperationTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInverseUnaryOperationTerm A) → (ClInverseUnaryOperationTerm A)) 
  | (invCl x1) := (invCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInverseUnaryOperationTerm n) → (OpInverseUnaryOperationTerm n)) 
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInverseUnaryOperationTerm2 n A) → (OpInverseUnaryOperationTerm2 n A)) 
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InverseUnaryOperation A) → (InverseUnaryOperationTerm → A)) 
  | In (invL x1) := ((inv In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InverseUnaryOperation A) → ((ClInverseUnaryOperationTerm A) → A)) 
  | In (sing x1) := x1  
  | In (invCl x1) := ((inv In) (evalCl In x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InverseUnaryOperation A) → ((vector A n) → ((OpInverseUnaryOperationTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (invOL x1) := ((inv In) (evalOpB In vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((InverseUnaryOperation A) → ((vector A n) → ((OpInverseUnaryOperationTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (invOL2 x1) := ((inv In) (evalOp In vars x1))  
  def inductionB   {P : (InverseUnaryOperationTerm → Type)}  : ((∀ (x1 : InverseUnaryOperationTerm) , ((P x1) → (P (invL x1)))) → (∀ (x : InverseUnaryOperationTerm) , (P x))) 
  | pinvl (invL x1) := (pinvl _ (inductionB pinvl x1))  
  def inductionCl   {A : Type} {P : ((ClInverseUnaryOperationTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInverseUnaryOperationTerm A)) , ((P x1) → (P (invCl x1)))) → (∀ (x : (ClInverseUnaryOperationTerm A)) , (P x)))) 
  | psing pinvcl (sing x1) := (psing x1)  
  | psing pinvcl (invCl x1) := (pinvcl _ (inductionCl psing pinvcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpInverseUnaryOperationTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInverseUnaryOperationTerm n)) , ((P x1) → (P (invOL x1)))) → (∀ (x : (OpInverseUnaryOperationTerm n)) , (P x)))) 
  | pv pinvol (v x1) := (pv x1)  
  | pv pinvol (invOL x1) := (pinvol _ (inductionOpB pv pinvol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInverseUnaryOperationTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInverseUnaryOperationTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → (∀ (x : (OpInverseUnaryOperationTerm2 n A)) , (P x))))) 
  | pv2 psing2 pinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pinvol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 pinvol2 x1))  
  def stageB  : (InverseUnaryOperationTerm → (Staged InverseUnaryOperationTerm))
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClInverseUnaryOperationTerm A) → (Staged (ClInverseUnaryOperationTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpInverseUnaryOperationTerm n) → (Staged (OpInverseUnaryOperationTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInverseUnaryOperationTerm2 n A) → (Staged (OpInverseUnaryOperationTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (invT : ((Repr A) → (Repr A))) 
  
end InverseUnaryOperation