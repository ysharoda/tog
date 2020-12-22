import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MiddleAbsorption   
  structure MiddleAbsorption  (A : Type) : Type := 
       (op : (A → (A → A)))
       (middleAbsorb_times : (∀ {x y z : A} , (op (op x y) z) = (op x z))) 
  
  open MiddleAbsorption
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (middleAbsorb_timesP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP zP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mi1 : (MiddleAbsorption A1)) (Mi2 : (MiddleAbsorption A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Mi1) x1 x2)) = ((op Mi2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mi1 : (MiddleAbsorption A1)) (Mi2 : (MiddleAbsorption A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mi1) x1 x2) ((op Mi2) y1 y2)))))) 
  
  inductive MiddleAbsorptionTerm   : Type  
     | opL : (MiddleAbsorptionTerm → (MiddleAbsorptionTerm → MiddleAbsorptionTerm))  
      open MiddleAbsorptionTerm 
  
  inductive ClMiddleAbsorptionTerm  (A : Type) : Type  
     | sing : (A → ClMiddleAbsorptionTerm) 
     | opCl : (ClMiddleAbsorptionTerm → (ClMiddleAbsorptionTerm → ClMiddleAbsorptionTerm))  
      open ClMiddleAbsorptionTerm 
  
  inductive OpMiddleAbsorptionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMiddleAbsorptionTerm) 
     | opOL : (OpMiddleAbsorptionTerm → (OpMiddleAbsorptionTerm → OpMiddleAbsorptionTerm))  
      open OpMiddleAbsorptionTerm 
  
  inductive OpMiddleAbsorptionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMiddleAbsorptionTerm2) 
     | sing2 : (A → OpMiddleAbsorptionTerm2) 
     | opOL2 : (OpMiddleAbsorptionTerm2 → (OpMiddleAbsorptionTerm2 → OpMiddleAbsorptionTerm2))  
      open OpMiddleAbsorptionTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMiddleAbsorptionTerm A) → (ClMiddleAbsorptionTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMiddleAbsorptionTerm n) → (OpMiddleAbsorptionTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMiddleAbsorptionTerm2 n A) → (OpMiddleAbsorptionTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MiddleAbsorption A) → (MiddleAbsorptionTerm → A)) 
  | Mi (opL x1 x2) := ((op Mi) (evalB Mi x1) (evalB Mi x2))  
  def evalCl   {A : Type}  : ((MiddleAbsorption A) → ((ClMiddleAbsorptionTerm A) → A)) 
  | Mi (sing x1) := x1  
  | Mi (opCl x1 x2) := ((op Mi) (evalCl Mi x1) (evalCl Mi x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MiddleAbsorption A) → ((vector A n) → ((OpMiddleAbsorptionTerm n) → A))) 
  | Mi vars (v x1) := (nth vars x1)  
  | Mi vars (opOL x1 x2) := ((op Mi) (evalOpB Mi vars x1) (evalOpB Mi vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((MiddleAbsorption A) → ((vector A n) → ((OpMiddleAbsorptionTerm2 n A) → A))) 
  | Mi vars (v2 x1) := (nth vars x1)  
  | Mi vars (sing2 x1) := x1  
  | Mi vars (opOL2 x1 x2) := ((op Mi) (evalOp Mi vars x1) (evalOp Mi vars x2))  
  def inductionB   (P : (MiddleAbsorptionTerm → Type))  : ((∀ (x1 x2 : MiddleAbsorptionTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : MiddleAbsorptionTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClMiddleAbsorptionTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMiddleAbsorptionTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClMiddleAbsorptionTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpMiddleAbsorptionTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMiddleAbsorptionTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpMiddleAbsorptionTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMiddleAbsorptionTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMiddleAbsorptionTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpMiddleAbsorptionTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (MiddleAbsorptionTerm → (Staged MiddleAbsorptionTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClMiddleAbsorptionTerm A) → (Staged (ClMiddleAbsorptionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpMiddleAbsorptionTerm n) → (Staged (OpMiddleAbsorptionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMiddleAbsorptionTerm2 n A) → (Staged (OpMiddleAbsorptionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MiddleAbsorption