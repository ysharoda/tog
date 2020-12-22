import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Kei   
  structure Kei  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z))))
       (idempotent_linv : (∀ {x : A} , (linv x x) = x))
       (rightSelfInverse_linv : (∀ {x y : A} , (linv (linv x y) y) = x)) 
  
  open Kei
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP))))
       (idempotent_linvP : (∀ {xP : (Prod A A)} , (linvP xP xP) = xP))
       (rightSelfInverse_linvP : (∀ {xP yP : (Prod A A)} , (linvP (linvP xP yP) yP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ke1 : (Kei A1)) (Ke2 : (Kei A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Ke1) x1 x2)) = ((linv Ke2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ke1 : (Kei A1)) (Ke2 : (Kei A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Ke1) x1 x2) ((linv Ke2) y1 y2)))))) 
  
  inductive KeiTerm   : Type  
     | linvL : (KeiTerm → (KeiTerm → KeiTerm))  
      open KeiTerm 
  
  inductive ClKeiTerm  (A : Type) : Type  
     | sing : (A → ClKeiTerm) 
     | linvCl : (ClKeiTerm → (ClKeiTerm → ClKeiTerm))  
      open ClKeiTerm 
  
  inductive OpKeiTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpKeiTerm) 
     | linvOL : (OpKeiTerm → (OpKeiTerm → OpKeiTerm))  
      open OpKeiTerm 
  
  inductive OpKeiTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpKeiTerm2) 
     | sing2 : (A → OpKeiTerm2) 
     | linvOL2 : (OpKeiTerm2 → (OpKeiTerm2 → OpKeiTerm2))  
      open OpKeiTerm2 
  
  def simplifyCl   (A : Type)  : ((ClKeiTerm A) → (ClKeiTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpKeiTerm n) → (OpKeiTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpKeiTerm2 n A) → (OpKeiTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Kei A) → (KeiTerm → A)) 
  | Ke (linvL x1 x2) := ((linv Ke) (evalB Ke x1) (evalB Ke x2))  
  def evalCl   {A : Type}  : ((Kei A) → ((ClKeiTerm A) → A)) 
  | Ke (sing x1) := x1  
  | Ke (linvCl x1 x2) := ((linv Ke) (evalCl Ke x1) (evalCl Ke x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Kei A) → ((vector A n) → ((OpKeiTerm n) → A))) 
  | Ke vars (v x1) := (nth vars x1)  
  | Ke vars (linvOL x1 x2) := ((linv Ke) (evalOpB Ke vars x1) (evalOpB Ke vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Kei A) → ((vector A n) → ((OpKeiTerm2 n A) → A))) 
  | Ke vars (v2 x1) := (nth vars x1)  
  | Ke vars (sing2 x1) := x1  
  | Ke vars (linvOL2 x1 x2) := ((linv Ke) (evalOp Ke vars x1) (evalOp Ke vars x2))  
  def inductionB   (P : (KeiTerm → Type))  : ((∀ (x1 x2 : KeiTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (∀ (x : KeiTerm) , (P x))) 
  | plinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl x1) (inductionB plinvl x2))  
  def inductionCl   (A : Type) (P : ((ClKeiTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClKeiTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (∀ (x : (ClKeiTerm A)) , (P x)))) 
  | psing plinvcl (sing x1) := (psing x1)  
  | psing plinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl x1) (inductionCl psing plinvcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpKeiTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpKeiTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (∀ (x : (OpKeiTerm n)) , (P x)))) 
  | pv plinvol (v x1) := (pv x1)  
  | pv plinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol x1) (inductionOpB pv plinvol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpKeiTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpKeiTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (∀ (x : (OpKeiTerm2 n A)) , (P x))))) 
  | pv2 psing2 plinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 x1) (inductionOp pv2 psing2 plinvol2 x2))  
  def stageB  : (KeiTerm → (Staged KeiTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClKeiTerm A) → (Staged (ClKeiTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpKeiTerm n) → (Staged (OpKeiTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpKeiTerm2 n A) → (Staged (OpKeiTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Kei