import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section IdempotentMagma   
  structure IdempotentMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (idempotent_op : (∀ {x : A} , (op x x) = x)) 
  
  open IdempotentMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (idempotent_opP : (∀ {xP : (Prod A A)} , (opP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Id1 : (IdempotentMagma A1)) (Id2 : (IdempotentMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Id1) x1 x2)) = ((op Id2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Id1 : (IdempotentMagma A1)) (Id2 : (IdempotentMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Id1) x1 x2) ((op Id2) y1 y2)))))) 
  
  inductive IdempotentMagmaTerm   : Type  
     | opL : (IdempotentMagmaTerm → (IdempotentMagmaTerm → IdempotentMagmaTerm))  
      open IdempotentMagmaTerm 
  
  inductive ClIdempotentMagmaTerm  (A : Type) : Type  
     | sing : (A → ClIdempotentMagmaTerm) 
     | opCl : (ClIdempotentMagmaTerm → (ClIdempotentMagmaTerm → ClIdempotentMagmaTerm))  
      open ClIdempotentMagmaTerm 
  
  inductive OpIdempotentMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpIdempotentMagmaTerm) 
     | opOL : (OpIdempotentMagmaTerm → (OpIdempotentMagmaTerm → OpIdempotentMagmaTerm))  
      open OpIdempotentMagmaTerm 
  
  inductive OpIdempotentMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpIdempotentMagmaTerm2) 
     | sing2 : (A → OpIdempotentMagmaTerm2) 
     | opOL2 : (OpIdempotentMagmaTerm2 → (OpIdempotentMagmaTerm2 → OpIdempotentMagmaTerm2))  
      open OpIdempotentMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClIdempotentMagmaTerm A) → (ClIdempotentMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpIdempotentMagmaTerm n) → (OpIdempotentMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpIdempotentMagmaTerm2 n A) → (OpIdempotentMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((IdempotentMagma A) → (IdempotentMagmaTerm → A)) 
  | Id (opL x1 x2) := ((op Id) (evalB Id x1) (evalB Id x2))  
  def evalCl   {A : Type}  : ((IdempotentMagma A) → ((ClIdempotentMagmaTerm A) → A)) 
  | Id (sing x1) := x1  
  | Id (opCl x1 x2) := ((op Id) (evalCl Id x1) (evalCl Id x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((IdempotentMagma A) → ((vector A n) → ((OpIdempotentMagmaTerm n) → A))) 
  | Id vars (v x1) := (nth vars x1)  
  | Id vars (opOL x1 x2) := ((op Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((IdempotentMagma A) → ((vector A n) → ((OpIdempotentMagmaTerm2 n A) → A))) 
  | Id vars (v2 x1) := (nth vars x1)  
  | Id vars (sing2 x1) := x1  
  | Id vars (opOL2 x1 x2) := ((op Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  def inductionB   (P : (IdempotentMagmaTerm → Type))  : ((∀ (x1 x2 : IdempotentMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : IdempotentMagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClIdempotentMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClIdempotentMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClIdempotentMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpIdempotentMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpIdempotentMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpIdempotentMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpIdempotentMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpIdempotentMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpIdempotentMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (IdempotentMagmaTerm → (Staged IdempotentMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClIdempotentMagmaTerm A) → (Staged (ClIdempotentMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpIdempotentMagmaTerm n) → (Staged (OpIdempotentMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpIdempotentMagmaTerm2 n A) → (Staged (OpIdempotentMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end IdempotentMagma