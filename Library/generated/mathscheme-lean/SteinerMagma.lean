import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section SteinerMagma   
  structure SteinerMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x)))
       (antiAbsorbent : (∀ {x y : A} , (op x (op x y)) = y)) 
  
  open SteinerMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP)))
       (antiAbsorbentP : (∀ {xP yP : (Prod A A)} , (opP xP (opP xP yP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (St1 : (SteinerMagma A1)) (St2 : (SteinerMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op St1) x1 x2)) = ((op St2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (St1 : (SteinerMagma A1)) (St2 : (SteinerMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op St1) x1 x2) ((op St2) y1 y2)))))) 
  
  inductive SteinerMagmaTerm   : Type  
     | opL : (SteinerMagmaTerm → (SteinerMagmaTerm → SteinerMagmaTerm))  
      open SteinerMagmaTerm 
  
  inductive ClSteinerMagmaTerm  (A : Type) : Type  
     | sing : (A → ClSteinerMagmaTerm) 
     | opCl : (ClSteinerMagmaTerm → (ClSteinerMagmaTerm → ClSteinerMagmaTerm))  
      open ClSteinerMagmaTerm 
  
  inductive OpSteinerMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSteinerMagmaTerm) 
     | opOL : (OpSteinerMagmaTerm → (OpSteinerMagmaTerm → OpSteinerMagmaTerm))  
      open OpSteinerMagmaTerm 
  
  inductive OpSteinerMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSteinerMagmaTerm2) 
     | sing2 : (A → OpSteinerMagmaTerm2) 
     | opOL2 : (OpSteinerMagmaTerm2 → (OpSteinerMagmaTerm2 → OpSteinerMagmaTerm2))  
      open OpSteinerMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClSteinerMagmaTerm A) → (ClSteinerMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpSteinerMagmaTerm n) → (OpSteinerMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpSteinerMagmaTerm2 n A) → (OpSteinerMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((SteinerMagma A) → (SteinerMagmaTerm → A)) 
  | St (opL x1 x2) := ((op St) (evalB St x1) (evalB St x2))  
  def evalCl   {A : Type}  : ((SteinerMagma A) → ((ClSteinerMagmaTerm A) → A)) 
  | St (sing x1) := x1  
  | St (opCl x1 x2) := ((op St) (evalCl St x1) (evalCl St x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((SteinerMagma A) → ((vector A n) → ((OpSteinerMagmaTerm n) → A))) 
  | St vars (v x1) := (nth vars x1)  
  | St vars (opOL x1 x2) := ((op St) (evalOpB St vars x1) (evalOpB St vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((SteinerMagma A) → ((vector A n) → ((OpSteinerMagmaTerm2 n A) → A))) 
  | St vars (v2 x1) := (nth vars x1)  
  | St vars (sing2 x1) := x1  
  | St vars (opOL2 x1 x2) := ((op St) (evalOp St vars x1) (evalOp St vars x2))  
  def inductionB   {P : (SteinerMagmaTerm → Type)}  : ((∀ (x1 x2 : SteinerMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : SteinerMagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   {A : Type} {P : ((ClSteinerMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClSteinerMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClSteinerMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpSteinerMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpSteinerMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpSteinerMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpSteinerMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpSteinerMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpSteinerMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (SteinerMagmaTerm → (Staged SteinerMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClSteinerMagmaTerm A) → (Staged (ClSteinerMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpSteinerMagmaTerm n) → (Staged (OpSteinerMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpSteinerMagmaTerm2 n A) → (Staged (OpSteinerMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end SteinerMagma