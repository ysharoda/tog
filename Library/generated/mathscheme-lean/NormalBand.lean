import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section NormalBand   
  structure NormalBand  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (idempotent_op : (∀ {x : A} , (op x x) = x))
       (middleCommute_times : (∀ {x y z : A} , (op (op (op x y) z) x) = (op (op (op x z) y) x))) 
  
  open NormalBand
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (idempotent_opP : (∀ {xP : (Prod A A)} , (opP xP xP) = xP))
       (middleCommute_timesP : (∀ {xP yP zP : (Prod A A)} , (opP (opP (opP xP yP) zP) xP) = (opP (opP (opP xP zP) yP) xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (No1 : (NormalBand A1)) (No2 : (NormalBand A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op No1) x1 x2)) = ((op No2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (No1 : (NormalBand A1)) (No2 : (NormalBand A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op No1) x1 x2) ((op No2) y1 y2)))))) 
  
  inductive NormalBandTerm   : Type  
     | opL : (NormalBandTerm → (NormalBandTerm → NormalBandTerm))  
      open NormalBandTerm 
  
  inductive ClNormalBandTerm  (A : Type) : Type  
     | sing : (A → ClNormalBandTerm) 
     | opCl : (ClNormalBandTerm → (ClNormalBandTerm → ClNormalBandTerm))  
      open ClNormalBandTerm 
  
  inductive OpNormalBandTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpNormalBandTerm) 
     | opOL : (OpNormalBandTerm → (OpNormalBandTerm → OpNormalBandTerm))  
      open OpNormalBandTerm 
  
  inductive OpNormalBandTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpNormalBandTerm2) 
     | sing2 : (A → OpNormalBandTerm2) 
     | opOL2 : (OpNormalBandTerm2 → (OpNormalBandTerm2 → OpNormalBandTerm2))  
      open OpNormalBandTerm2 
  
  def simplifyCl   {A : Type}  : ((ClNormalBandTerm A) → (ClNormalBandTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpNormalBandTerm n) → (OpNormalBandTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpNormalBandTerm2 n A) → (OpNormalBandTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((NormalBand A) → (NormalBandTerm → A)) 
  | No (opL x1 x2) := ((op No) (evalB No x1) (evalB No x2))  
  def evalCl   {A : Type}  : ((NormalBand A) → ((ClNormalBandTerm A) → A)) 
  | No (sing x1) := x1  
  | No (opCl x1 x2) := ((op No) (evalCl No x1) (evalCl No x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((NormalBand A) → ((vector A n) → ((OpNormalBandTerm n) → A))) 
  | No vars (v x1) := (nth vars x1)  
  | No vars (opOL x1 x2) := ((op No) (evalOpB No vars x1) (evalOpB No vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((NormalBand A) → ((vector A n) → ((OpNormalBandTerm2 n A) → A))) 
  | No vars (v2 x1) := (nth vars x1)  
  | No vars (sing2 x1) := x1  
  | No vars (opOL2 x1 x2) := ((op No) (evalOp No vars x1) (evalOp No vars x2))  
  def inductionB   {P : (NormalBandTerm → Type)}  : ((∀ (x1 x2 : NormalBandTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : NormalBandTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClNormalBandTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClNormalBandTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClNormalBandTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpNormalBandTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpNormalBandTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpNormalBandTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpNormalBandTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpNormalBandTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpNormalBandTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (NormalBandTerm → (Staged NormalBandTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClNormalBandTerm A) → (Staged (ClNormalBandTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpNormalBandTerm n) → (Staged (OpNormalBandTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpNormalBandTerm2 n A) → (Staged (OpNormalBandTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end NormalBand