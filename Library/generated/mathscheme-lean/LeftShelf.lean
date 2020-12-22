import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftShelf   
  structure LeftShelf  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z)))) 
  
  open LeftShelf
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftShelf A1)) (Le2 : (LeftShelf A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Le1) x1 x2)) = ((linv Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftShelf A1)) (Le2 : (LeftShelf A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2)))))) 
  
  inductive LeftShelfTerm   : Type  
     | linvL : (LeftShelfTerm → (LeftShelfTerm → LeftShelfTerm))  
      open LeftShelfTerm 
  
  inductive ClLeftShelfTerm  (A : Type) : Type  
     | sing : (A → ClLeftShelfTerm) 
     | linvCl : (ClLeftShelfTerm → (ClLeftShelfTerm → ClLeftShelfTerm))  
      open ClLeftShelfTerm 
  
  inductive OpLeftShelfTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftShelfTerm) 
     | linvOL : (OpLeftShelfTerm → (OpLeftShelfTerm → OpLeftShelfTerm))  
      open OpLeftShelfTerm 
  
  inductive OpLeftShelfTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftShelfTerm2) 
     | sing2 : (A → OpLeftShelfTerm2) 
     | linvOL2 : (OpLeftShelfTerm2 → (OpLeftShelfTerm2 → OpLeftShelfTerm2))  
      open OpLeftShelfTerm2 
  
  def simplifyCl   (A : Type)  : ((ClLeftShelfTerm A) → (ClLeftShelfTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpLeftShelfTerm n) → (OpLeftShelfTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpLeftShelfTerm2 n A) → (OpLeftShelfTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftShelf A) → (LeftShelfTerm → A)) 
  | Le (linvL x1 x2) := ((linv Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftShelf A) → ((ClLeftShelfTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (linvCl x1 x2) := ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((LeftShelf A) → ((vector A n) → ((OpLeftShelfTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (linvOL x1 x2) := ((linv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((LeftShelf A) → ((vector A n) → ((OpLeftShelfTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (linvOL2 x1 x2) := ((linv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   (P : (LeftShelfTerm → Type))  : ((∀ (x1 x2 : LeftShelfTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (∀ (x : LeftShelfTerm) , (P x))) 
  | plinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl x1) (inductionB plinvl x2))  
  def inductionCl   (A : Type) (P : ((ClLeftShelfTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftShelfTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (∀ (x : (ClLeftShelfTerm A)) , (P x)))) 
  | psing plinvcl (sing x1) := (psing x1)  
  | psing plinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl x1) (inductionCl psing plinvcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpLeftShelfTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftShelfTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (∀ (x : (OpLeftShelfTerm n)) , (P x)))) 
  | pv plinvol (v x1) := (pv x1)  
  | pv plinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol x1) (inductionOpB pv plinvol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpLeftShelfTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftShelfTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (∀ (x : (OpLeftShelfTerm2 n A)) , (P x))))) 
  | pv2 psing2 plinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 x1) (inductionOp pv2 psing2 plinvol2 x2))  
  def stageB  : (LeftShelfTerm → (Staged LeftShelfTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClLeftShelfTerm A) → (Staged (ClLeftShelfTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpLeftShelfTerm n) → (Staged (OpLeftShelfTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpLeftShelfTerm2 n A) → (Staged (OpLeftShelfTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftShelf