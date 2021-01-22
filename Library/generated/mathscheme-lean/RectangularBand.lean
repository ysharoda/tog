import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RectangularBand   
  structure RectangularBand  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (idempotent_op : (∀ {x : A} , (op x x) = x))
       (middleCommute_times : (∀ {x y z : A} , (op (op (op x y) z) x) = (op (op (op x z) y) x))) 
  
  open RectangularBand
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (idempotent_opP : (∀ {xP : (Prod A A)} , (opP xP xP) = xP))
       (middleCommute_timesP : (∀ {xP yP zP : (Prod A A)} , (opP (opP (opP xP yP) zP) xP) = (opP (opP (opP xP zP) yP) xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Re1 : (RectangularBand A1)) (Re2 : (RectangularBand A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Re1) x1 x2)) = ((op Re2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Re1 : (RectangularBand A1)) (Re2 : (RectangularBand A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Re1) x1 x2) ((op Re2) y1 y2)))))) 
  
  inductive RectangularBandTerm   : Type  
     | opL : (RectangularBandTerm → (RectangularBandTerm → RectangularBandTerm))  
      open RectangularBandTerm 
  
  inductive ClRectangularBandTerm  (A : Type) : Type  
     | sing : (A → ClRectangularBandTerm) 
     | opCl : (ClRectangularBandTerm → (ClRectangularBandTerm → ClRectangularBandTerm))  
      open ClRectangularBandTerm 
  
  inductive OpRectangularBandTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRectangularBandTerm) 
     | opOL : (OpRectangularBandTerm → (OpRectangularBandTerm → OpRectangularBandTerm))  
      open OpRectangularBandTerm 
  
  inductive OpRectangularBandTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRectangularBandTerm2) 
     | sing2 : (A → OpRectangularBandTerm2) 
     | opOL2 : (OpRectangularBandTerm2 → (OpRectangularBandTerm2 → OpRectangularBandTerm2))  
      open OpRectangularBandTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRectangularBandTerm A) → (ClRectangularBandTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRectangularBandTerm n) → (OpRectangularBandTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRectangularBandTerm2 n A) → (OpRectangularBandTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RectangularBand A) → (RectangularBandTerm → A)) 
  | Re (opL x1 x2) := ((op Re) (evalB Re x1) (evalB Re x2))  
  def evalCl   {A : Type}  : ((RectangularBand A) → ((ClRectangularBandTerm A) → A)) 
  | Re (sing x1) := x1  
  | Re (opCl x1 x2) := ((op Re) (evalCl Re x1) (evalCl Re x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RectangularBand A) → ((vector A n) → ((OpRectangularBandTerm n) → A))) 
  | Re vars (v x1) := (nth vars x1)  
  | Re vars (opOL x1 x2) := ((op Re) (evalOpB Re vars x1) (evalOpB Re vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RectangularBand A) → ((vector A n) → ((OpRectangularBandTerm2 n A) → A))) 
  | Re vars (v2 x1) := (nth vars x1)  
  | Re vars (sing2 x1) := x1  
  | Re vars (opOL2 x1 x2) := ((op Re) (evalOp Re vars x1) (evalOp Re vars x2))  
  def inductionB   {P : (RectangularBandTerm → Type)}  : ((∀ (x1 x2 : RectangularBandTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : RectangularBandTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClRectangularBandTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRectangularBandTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClRectangularBandTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRectangularBandTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRectangularBandTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpRectangularBandTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRectangularBandTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRectangularBandTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpRectangularBandTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (RectangularBandTerm → (Staged RectangularBandTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRectangularBandTerm A) → (Staged (ClRectangularBandTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRectangularBandTerm n) → (Staged (OpRectangularBandTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRectangularBandTerm2 n A) → (Staged (OpRectangularBandTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RectangularBand