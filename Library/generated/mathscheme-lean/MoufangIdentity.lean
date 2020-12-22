import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MoufangIdentity   
  structure MoufangIdentity  (A : Type) : Type := 
       (op : (A → (A → A)))
       (moufangId : (∀ {x y z : A} , (op (op z x) (op y z)) = (op (op z (op x y)) z))) 
  
  open MoufangIdentity
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (moufangIdP : (∀ {xP yP zP : (Prod A A)} , (opP (opP zP xP) (opP yP zP)) = (opP (opP zP (opP xP yP)) zP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mo1 : (MoufangIdentity A1)) (Mo2 : (MoufangIdentity A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Mo1) x1 x2)) = ((op Mo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mo1 : (MoufangIdentity A1)) (Mo2 : (MoufangIdentity A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2)))))) 
  
  inductive MoufangIdentityTerm   : Type  
     | opL : (MoufangIdentityTerm → (MoufangIdentityTerm → MoufangIdentityTerm))  
      open MoufangIdentityTerm 
  
  inductive ClMoufangIdentityTerm  (A : Type) : Type  
     | sing : (A → ClMoufangIdentityTerm) 
     | opCl : (ClMoufangIdentityTerm → (ClMoufangIdentityTerm → ClMoufangIdentityTerm))  
      open ClMoufangIdentityTerm 
  
  inductive OpMoufangIdentityTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMoufangIdentityTerm) 
     | opOL : (OpMoufangIdentityTerm → (OpMoufangIdentityTerm → OpMoufangIdentityTerm))  
      open OpMoufangIdentityTerm 
  
  inductive OpMoufangIdentityTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMoufangIdentityTerm2) 
     | sing2 : (A → OpMoufangIdentityTerm2) 
     | opOL2 : (OpMoufangIdentityTerm2 → (OpMoufangIdentityTerm2 → OpMoufangIdentityTerm2))  
      open OpMoufangIdentityTerm2 
  
  def simplifyCl   (A : Type)  : ((ClMoufangIdentityTerm A) → (ClMoufangIdentityTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpMoufangIdentityTerm n) → (OpMoufangIdentityTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpMoufangIdentityTerm2 n A) → (OpMoufangIdentityTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MoufangIdentity A) → (MoufangIdentityTerm → A)) 
  | Mo (opL x1 x2) := ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  def evalCl   {A : Type}  : ((MoufangIdentity A) → ((ClMoufangIdentityTerm A) → A)) 
  | Mo (sing x1) := x1  
  | Mo (opCl x1 x2) := ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((MoufangIdentity A) → ((vector A n) → ((OpMoufangIdentityTerm n) → A))) 
  | Mo vars (v x1) := (nth vars x1)  
  | Mo vars (opOL x1 x2) := ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((MoufangIdentity A) → ((vector A n) → ((OpMoufangIdentityTerm2 n A) → A))) 
  | Mo vars (v2 x1) := (nth vars x1)  
  | Mo vars (sing2 x1) := x1  
  | Mo vars (opOL2 x1 x2) := ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  def inductionB   (P : (MoufangIdentityTerm → Type))  : ((∀ (x1 x2 : MoufangIdentityTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : MoufangIdentityTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClMoufangIdentityTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMoufangIdentityTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClMoufangIdentityTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpMoufangIdentityTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMoufangIdentityTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpMoufangIdentityTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpMoufangIdentityTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMoufangIdentityTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpMoufangIdentityTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (MoufangIdentityTerm → (Staged MoufangIdentityTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClMoufangIdentityTerm A) → (Staged (ClMoufangIdentityTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpMoufangIdentityTerm n) → (Staged (OpMoufangIdentityTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpMoufangIdentityTerm2 n A) → (Staged (OpMoufangIdentityTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MoufangIdentity