import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section IdempotentMultMagma   
  structure IdempotentMultMagma  (A : Type) : Type := 
       (times : (A → (A → A)))
       (idempotent_times : (∀ {x : A} , (times x x) = x)) 
  
  open IdempotentMultMagma
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Id1 : (IdempotentMultMagma A1)) (Id2 : (IdempotentMultMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Id1) x1 x2)) = ((times Id2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Id1 : (IdempotentMultMagma A1)) (Id2 : (IdempotentMultMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Id1) x1 x2) ((times Id2) y1 y2)))))) 
  
  inductive IdempotentMultMagmaTerm   : Type  
     | timesL : (IdempotentMultMagmaTerm → (IdempotentMultMagmaTerm → IdempotentMultMagmaTerm))  
      open IdempotentMultMagmaTerm 
  
  inductive ClIdempotentMultMagmaTerm  (A : Type) : Type  
     | sing : (A → ClIdempotentMultMagmaTerm) 
     | timesCl : (ClIdempotentMultMagmaTerm → (ClIdempotentMultMagmaTerm → ClIdempotentMultMagmaTerm))  
      open ClIdempotentMultMagmaTerm 
  
  inductive OpIdempotentMultMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpIdempotentMultMagmaTerm) 
     | timesOL : (OpIdempotentMultMagmaTerm → (OpIdempotentMultMagmaTerm → OpIdempotentMultMagmaTerm))  
      open OpIdempotentMultMagmaTerm 
  
  inductive OpIdempotentMultMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpIdempotentMultMagmaTerm2) 
     | sing2 : (A → OpIdempotentMultMagmaTerm2) 
     | timesOL2 : (OpIdempotentMultMagmaTerm2 → (OpIdempotentMultMagmaTerm2 → OpIdempotentMultMagmaTerm2))  
      open OpIdempotentMultMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClIdempotentMultMagmaTerm A) → (ClIdempotentMultMagmaTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpIdempotentMultMagmaTerm n) → (OpIdempotentMultMagmaTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpIdempotentMultMagmaTerm2 n A) → (OpIdempotentMultMagmaTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((IdempotentMultMagma A) → (IdempotentMultMagmaTerm → A)) 
  | Id (timesL x1 x2) := ((times Id) (evalB Id x1) (evalB Id x2))  
  def evalCl   {A : Type}  : ((IdempotentMultMagma A) → ((ClIdempotentMultMagmaTerm A) → A)) 
  | Id (sing x1) := x1  
  | Id (timesCl x1 x2) := ((times Id) (evalCl Id x1) (evalCl Id x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((IdempotentMultMagma A) → ((vector A n) → ((OpIdempotentMultMagmaTerm n) → A))) 
  | Id vars (v x1) := (nth vars x1)  
  | Id vars (timesOL x1 x2) := ((times Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((IdempotentMultMagma A) → ((vector A n) → ((OpIdempotentMultMagmaTerm2 n A) → A))) 
  | Id vars (v2 x1) := (nth vars x1)  
  | Id vars (sing2 x1) := x1  
  | Id vars (timesOL2 x1 x2) := ((times Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  def inductionB   (P : (IdempotentMultMagmaTerm → Type))  : ((∀ (x1 x2 : IdempotentMultMagmaTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : IdempotentMultMagmaTerm) , (P x))) 
  | ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl x1) (inductionB ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClIdempotentMultMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClIdempotentMultMagmaTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClIdempotentMultMagmaTerm A)) , (P x)))) 
  | psing ptimescl (sing x1) := (psing x1)  
  | psing ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl x1) (inductionCl psing ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpIdempotentMultMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpIdempotentMultMagmaTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpIdempotentMultMagmaTerm n)) , (P x)))) 
  | pv ptimesol (v x1) := (pv x1)  
  | pv ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol x1) (inductionOpB pv ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpIdempotentMultMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpIdempotentMultMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpIdempotentMultMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 x1) (inductionOp pv2 psing2 ptimesol2 x2))  
  def stageB  : (IdempotentMultMagmaTerm → (Staged IdempotentMultMagmaTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClIdempotentMultMagmaTerm A) → (Staged (ClIdempotentMultMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpIdempotentMultMagmaTerm n) → (Staged (OpIdempotentMultMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpIdempotentMultMagmaTerm2 n A) → (Staged (OpIdempotentMultMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end IdempotentMultMagma