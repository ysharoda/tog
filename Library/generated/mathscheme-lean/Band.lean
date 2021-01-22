import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Band   
  structure Band  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (idempotent_op : (∀ {x : A} , (op x x) = x)) 
  
  open Band
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (idempotent_opP : (∀ {xP : (Prod A A)} , (opP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ba1 : (Band A1)) (Ba2 : (Band A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ba1) x1 x2)) = ((op Ba2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ba1 : (Band A1)) (Ba2 : (Band A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ba1) x1 x2) ((op Ba2) y1 y2)))))) 
  
  inductive BandTerm   : Type  
     | opL : (BandTerm → (BandTerm → BandTerm))  
      open BandTerm 
  
  inductive ClBandTerm  (A : Type) : Type  
     | sing : (A → ClBandTerm) 
     | opCl : (ClBandTerm → (ClBandTerm → ClBandTerm))  
      open ClBandTerm 
  
  inductive OpBandTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBandTerm) 
     | opOL : (OpBandTerm → (OpBandTerm → OpBandTerm))  
      open OpBandTerm 
  
  inductive OpBandTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBandTerm2) 
     | sing2 : (A → OpBandTerm2) 
     | opOL2 : (OpBandTerm2 → (OpBandTerm2 → OpBandTerm2))  
      open OpBandTerm2 
  
  def simplifyCl   {A : Type}  : ((ClBandTerm A) → (ClBandTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpBandTerm n) → (OpBandTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpBandTerm2 n A) → (OpBandTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Band A) → (BandTerm → A)) 
  | Ba (opL x1 x2) := ((op Ba) (evalB Ba x1) (evalB Ba x2))  
  def evalCl   {A : Type}  : ((Band A) → ((ClBandTerm A) → A)) 
  | Ba (sing x1) := x1  
  | Ba (opCl x1 x2) := ((op Ba) (evalCl Ba x1) (evalCl Ba x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Band A) → ((vector A n) → ((OpBandTerm n) → A))) 
  | Ba vars (v x1) := (nth vars x1)  
  | Ba vars (opOL x1 x2) := ((op Ba) (evalOpB Ba vars x1) (evalOpB Ba vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Band A) → ((vector A n) → ((OpBandTerm2 n A) → A))) 
  | Ba vars (v2 x1) := (nth vars x1)  
  | Ba vars (sing2 x1) := x1  
  | Ba vars (opOL2 x1 x2) := ((op Ba) (evalOp Ba vars x1) (evalOp Ba vars x2))  
  def inductionB   {P : (BandTerm → Type)}  : ((∀ (x1 x2 : BandTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : BandTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClBandTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBandTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClBandTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpBandTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBandTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpBandTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpBandTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBandTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpBandTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (BandTerm → (Staged BandTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClBandTerm A) → (Staged (ClBandTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpBandTerm n) → (Staged (OpBandTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpBandTerm2 n A) → (Staged (OpBandTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Band