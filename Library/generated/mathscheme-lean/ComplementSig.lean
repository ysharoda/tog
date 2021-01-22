import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section ComplementSig   
  structure ComplementSig  (A : Type) : Type := 
       (compl : (A → A)) 
  
  open ComplementSig
  structure Sig  (AS : Type) : Type := 
       (complS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (complP : ((Prod A A) → (Prod A A))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (ComplementSig A1)) (Co2 : (ComplementSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_compl : (∀ {x1 : A1} , (hom ((compl Co1) x1)) = ((compl Co2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (ComplementSig A1)) (Co2 : (ComplementSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_compl : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((compl Co1) x1) ((compl Co2) y1))))) 
  
  inductive ComplementSigTerm   : Type  
     | complL : (ComplementSigTerm → ComplementSigTerm)  
      open ComplementSigTerm 
  
  inductive ClComplementSigTerm  (A : Type) : Type  
     | sing : (A → ClComplementSigTerm) 
     | complCl : (ClComplementSigTerm → ClComplementSigTerm)  
      open ClComplementSigTerm 
  
  inductive OpComplementSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpComplementSigTerm) 
     | complOL : (OpComplementSigTerm → OpComplementSigTerm)  
      open OpComplementSigTerm 
  
  inductive OpComplementSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpComplementSigTerm2) 
     | sing2 : (A → OpComplementSigTerm2) 
     | complOL2 : (OpComplementSigTerm2 → OpComplementSigTerm2)  
      open OpComplementSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClComplementSigTerm A) → (ClComplementSigTerm A)) 
  | (complCl x1) := (complCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpComplementSigTerm n) → (OpComplementSigTerm n)) 
  | (complOL x1) := (complOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpComplementSigTerm2 n A) → (OpComplementSigTerm2 n A)) 
  | (complOL2 x1) := (complOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((ComplementSig A) → (ComplementSigTerm → A)) 
  | Co (complL x1) := ((compl Co) (evalB Co x1))  
  def evalCl   {A : Type}  : ((ComplementSig A) → ((ClComplementSigTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co (complCl x1) := ((compl Co) (evalCl Co x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((ComplementSig A) → ((vector A n) → ((OpComplementSigTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars (complOL x1) := ((compl Co) (evalOpB Co vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((ComplementSig A) → ((vector A n) → ((OpComplementSigTerm2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars (complOL2 x1) := ((compl Co) (evalOp Co vars x1))  
  def inductionB   {P : (ComplementSigTerm → Type)}  : ((∀ (x1 : ComplementSigTerm) , ((P x1) → (P (complL x1)))) → (∀ (x : ComplementSigTerm) , (P x))) 
  | pcompll (complL x1) := (pcompll _ (inductionB pcompll x1))  
  def inductionCl   {A : Type} {P : ((ClComplementSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClComplementSigTerm A)) , ((P x1) → (P (complCl x1)))) → (∀ (x : (ClComplementSigTerm A)) , (P x)))) 
  | psing pcomplcl (sing x1) := (psing x1)  
  | psing pcomplcl (complCl x1) := (pcomplcl _ (inductionCl psing pcomplcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpComplementSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpComplementSigTerm n)) , ((P x1) → (P (complOL x1)))) → (∀ (x : (OpComplementSigTerm n)) , (P x)))) 
  | pv pcomplol (v x1) := (pv x1)  
  | pv pcomplol (complOL x1) := (pcomplol _ (inductionOpB pv pcomplol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpComplementSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpComplementSigTerm2 n A)) , ((P x1) → (P (complOL2 x1)))) → (∀ (x : (OpComplementSigTerm2 n A)) , (P x))))) 
  | pv2 psing2 pcomplol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pcomplol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pcomplol2 (complOL2 x1) := (pcomplol2 _ (inductionOp pv2 psing2 pcomplol2 x1))  
  def stageB  : (ComplementSigTerm → (Staged ComplementSigTerm))
  | (complL x1) := (stage1 complL (codeLift1 complL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClComplementSigTerm A) → (Staged (ClComplementSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (complCl x1) := (stage1 complCl (codeLift1 complCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpComplementSigTerm n) → (Staged (OpComplementSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (complOL x1) := (stage1 complOL (codeLift1 complOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpComplementSigTerm2 n A) → (Staged (OpComplementSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (complOL2 x1) := (stage1 complOL2 (codeLift1 complOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (complT : ((Repr A) → (Repr A))) 
  
end ComplementSig