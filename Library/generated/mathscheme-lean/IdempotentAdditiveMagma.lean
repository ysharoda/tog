import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section IdempotentAdditiveMagma   
  structure IdempotentAdditiveMagma  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x)) 
  
  open IdempotentAdditiveMagma
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Id1 : (IdempotentAdditiveMagma A1)) (Id2 : (IdempotentAdditiveMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Id1) x1 x2)) = ((plus Id2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Id1 : (IdempotentAdditiveMagma A1)) (Id2 : (IdempotentAdditiveMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Id1) x1 x2) ((plus Id2) y1 y2)))))) 
  
  inductive IdempotentAdditiveMagmaTerm   : Type  
     | plusL : (IdempotentAdditiveMagmaTerm → (IdempotentAdditiveMagmaTerm → IdempotentAdditiveMagmaTerm))  
      open IdempotentAdditiveMagmaTerm 
  
  inductive ClIdempotentAdditiveMagmaTerm  (A : Type) : Type  
     | sing : (A → ClIdempotentAdditiveMagmaTerm) 
     | plusCl : (ClIdempotentAdditiveMagmaTerm → (ClIdempotentAdditiveMagmaTerm → ClIdempotentAdditiveMagmaTerm))  
      open ClIdempotentAdditiveMagmaTerm 
  
  inductive OpIdempotentAdditiveMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpIdempotentAdditiveMagmaTerm) 
     | plusOL : (OpIdempotentAdditiveMagmaTerm → (OpIdempotentAdditiveMagmaTerm → OpIdempotentAdditiveMagmaTerm))  
      open OpIdempotentAdditiveMagmaTerm 
  
  inductive OpIdempotentAdditiveMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpIdempotentAdditiveMagmaTerm2) 
     | sing2 : (A → OpIdempotentAdditiveMagmaTerm2) 
     | plusOL2 : (OpIdempotentAdditiveMagmaTerm2 → (OpIdempotentAdditiveMagmaTerm2 → OpIdempotentAdditiveMagmaTerm2))  
      open OpIdempotentAdditiveMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClIdempotentAdditiveMagmaTerm A) → (ClIdempotentAdditiveMagmaTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpIdempotentAdditiveMagmaTerm n) → (OpIdempotentAdditiveMagmaTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpIdempotentAdditiveMagmaTerm2 n A) → (OpIdempotentAdditiveMagmaTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((IdempotentAdditiveMagma A) → (IdempotentAdditiveMagmaTerm → A)) 
  | Id (plusL x1 x2) := ((plus Id) (evalB Id x1) (evalB Id x2))  
  def evalCl   {A : Type}  : ((IdempotentAdditiveMagma A) → ((ClIdempotentAdditiveMagmaTerm A) → A)) 
  | Id (sing x1) := x1  
  | Id (plusCl x1 x2) := ((plus Id) (evalCl Id x1) (evalCl Id x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((IdempotentAdditiveMagma A) → ((vector A n) → ((OpIdempotentAdditiveMagmaTerm n) → A))) 
  | Id vars (v x1) := (nth vars x1)  
  | Id vars (plusOL x1 x2) := ((plus Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((IdempotentAdditiveMagma A) → ((vector A n) → ((OpIdempotentAdditiveMagmaTerm2 n A) → A))) 
  | Id vars (v2 x1) := (nth vars x1)  
  | Id vars (sing2 x1) := x1  
  | Id vars (plusOL2 x1 x2) := ((plus Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  def inductionB   (P : (IdempotentAdditiveMagmaTerm → Type))  : ((∀ (x1 x2 : IdempotentAdditiveMagmaTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : IdempotentAdditiveMagmaTerm) , (P x))) 
  | pplusl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl x1) (inductionB pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClIdempotentAdditiveMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClIdempotentAdditiveMagmaTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClIdempotentAdditiveMagmaTerm A)) , (P x)))) 
  | psing ppluscl (sing x1) := (psing x1)  
  | psing ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl x1) (inductionCl psing ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpIdempotentAdditiveMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpIdempotentAdditiveMagmaTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpIdempotentAdditiveMagmaTerm n)) , (P x)))) 
  | pv pplusol (v x1) := (pv x1)  
  | pv pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol x1) (inductionOpB pv pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpIdempotentAdditiveMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpIdempotentAdditiveMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpIdempotentAdditiveMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 x1) (inductionOp pv2 psing2 pplusol2 x2))  
  def stageB  : (IdempotentAdditiveMagmaTerm → (Staged IdempotentAdditiveMagmaTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClIdempotentAdditiveMagmaTerm A) → (Staged (ClIdempotentAdditiveMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpIdempotentAdditiveMagmaTerm n) → (Staged (OpIdempotentAdditiveMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpIdempotentAdditiveMagmaTerm2 n A) → (Staged (OpIdempotentAdditiveMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end IdempotentAdditiveMagma