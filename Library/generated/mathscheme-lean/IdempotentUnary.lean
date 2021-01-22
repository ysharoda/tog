import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section IdempotentUnary   
  structure IdempotentUnary  (A : Type) : Type := 
       (prim : (A → A))
       (idempotent_prim : (∀ {x : A} , (prim (prim x)) = (prim x))) 
  
  open IdempotentUnary
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (idempotent_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = (primP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Id1 : (IdempotentUnary A1)) (Id2 : (IdempotentUnary A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Id1) x1)) = ((prim Id2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Id1 : (IdempotentUnary A1)) (Id2 : (IdempotentUnary A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Id1) x1) ((prim Id2) y1))))) 
  
  inductive IdempotentUnaryTerm   : Type  
     | primL : (IdempotentUnaryTerm → IdempotentUnaryTerm)  
      open IdempotentUnaryTerm 
  
  inductive ClIdempotentUnaryTerm  (A : Type) : Type  
     | sing : (A → ClIdempotentUnaryTerm) 
     | primCl : (ClIdempotentUnaryTerm → ClIdempotentUnaryTerm)  
      open ClIdempotentUnaryTerm 
  
  inductive OpIdempotentUnaryTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpIdempotentUnaryTerm) 
     | primOL : (OpIdempotentUnaryTerm → OpIdempotentUnaryTerm)  
      open OpIdempotentUnaryTerm 
  
  inductive OpIdempotentUnaryTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpIdempotentUnaryTerm2) 
     | sing2 : (A → OpIdempotentUnaryTerm2) 
     | primOL2 : (OpIdempotentUnaryTerm2 → OpIdempotentUnaryTerm2)  
      open OpIdempotentUnaryTerm2 
  
  def simplifyCl   {A : Type}  : ((ClIdempotentUnaryTerm A) → (ClIdempotentUnaryTerm A)) 
  | (primCl (primCl x)) := (primCl x)  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpIdempotentUnaryTerm n) → (OpIdempotentUnaryTerm n)) 
  | (primOL (primOL x)) := (primOL x)  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpIdempotentUnaryTerm2 n A) → (OpIdempotentUnaryTerm2 n A)) 
  | (primOL2 (primOL2 x)) := (primOL2 x)  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((IdempotentUnary A) → (IdempotentUnaryTerm → A)) 
  | Id (primL x1) := ((prim Id) (evalB Id x1))  
  def evalCl   {A : Type}  : ((IdempotentUnary A) → ((ClIdempotentUnaryTerm A) → A)) 
  | Id (sing x1) := x1  
  | Id (primCl x1) := ((prim Id) (evalCl Id x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((IdempotentUnary A) → ((vector A n) → ((OpIdempotentUnaryTerm n) → A))) 
  | Id vars (v x1) := (nth vars x1)  
  | Id vars (primOL x1) := ((prim Id) (evalOpB Id vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((IdempotentUnary A) → ((vector A n) → ((OpIdempotentUnaryTerm2 n A) → A))) 
  | Id vars (v2 x1) := (nth vars x1)  
  | Id vars (sing2 x1) := x1  
  | Id vars (primOL2 x1) := ((prim Id) (evalOp Id vars x1))  
  def inductionB   {P : (IdempotentUnaryTerm → Type)}  : ((∀ (x1 : IdempotentUnaryTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : IdempotentUnaryTerm) , (P x))) 
  | ppriml (primL x1) := (ppriml _ (inductionB ppriml x1))  
  def inductionCl   {A : Type} {P : ((ClIdempotentUnaryTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClIdempotentUnaryTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClIdempotentUnaryTerm A)) , (P x)))) 
  | psing pprimcl (sing x1) := (psing x1)  
  | psing pprimcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpIdempotentUnaryTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpIdempotentUnaryTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpIdempotentUnaryTerm n)) , (P x)))) 
  | pv pprimol (v x1) := (pv x1)  
  | pv pprimol (primOL x1) := (pprimol _ (inductionOpB pv pprimol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpIdempotentUnaryTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpIdempotentUnaryTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpIdempotentUnaryTerm2 n A)) , (P x))))) 
  | pv2 psing2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 x1))  
  def stageB  : (IdempotentUnaryTerm → (Staged IdempotentUnaryTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClIdempotentUnaryTerm A) → (Staged (ClIdempotentUnaryTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpIdempotentUnaryTerm n) → (Staged (OpIdempotentUnaryTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpIdempotentUnaryTerm2 n A) → (Staged (OpIdempotentUnaryTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A))) 
  
end IdempotentUnary