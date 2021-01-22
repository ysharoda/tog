import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftInverseMagma   
  structure LeftInverseMagma  (A : Type) : Type := 
       (linv : (A → (A → A))) 
  
  open LeftInverseMagma
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftInverseMagma A1)) (Le2 : (LeftInverseMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Le1) x1 x2)) = ((linv Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftInverseMagma A1)) (Le2 : (LeftInverseMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2)))))) 
  
  inductive LeftInverseMagmaTerm   : Type  
     | linvL : (LeftInverseMagmaTerm → (LeftInverseMagmaTerm → LeftInverseMagmaTerm))  
      open LeftInverseMagmaTerm 
  
  inductive ClLeftInverseMagmaTerm  (A : Type) : Type  
     | sing : (A → ClLeftInverseMagmaTerm) 
     | linvCl : (ClLeftInverseMagmaTerm → (ClLeftInverseMagmaTerm → ClLeftInverseMagmaTerm))  
      open ClLeftInverseMagmaTerm 
  
  inductive OpLeftInverseMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftInverseMagmaTerm) 
     | linvOL : (OpLeftInverseMagmaTerm → (OpLeftInverseMagmaTerm → OpLeftInverseMagmaTerm))  
      open OpLeftInverseMagmaTerm 
  
  inductive OpLeftInverseMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftInverseMagmaTerm2) 
     | sing2 : (A → OpLeftInverseMagmaTerm2) 
     | linvOL2 : (OpLeftInverseMagmaTerm2 → (OpLeftInverseMagmaTerm2 → OpLeftInverseMagmaTerm2))  
      open OpLeftInverseMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClLeftInverseMagmaTerm A) → (ClLeftInverseMagmaTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLeftInverseMagmaTerm n) → (OpLeftInverseMagmaTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLeftInverseMagmaTerm2 n A) → (OpLeftInverseMagmaTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftInverseMagma A) → (LeftInverseMagmaTerm → A)) 
  | Le (linvL x1 x2) := ((linv Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftInverseMagma A) → ((ClLeftInverseMagmaTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (linvCl x1 x2) := ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((LeftInverseMagma A) → ((vector A n) → ((OpLeftInverseMagmaTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (linvOL x1 x2) := ((linv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((LeftInverseMagma A) → ((vector A n) → ((OpLeftInverseMagmaTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (linvOL2 x1 x2) := ((linv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   {P : (LeftInverseMagmaTerm → Type)}  : ((∀ (x1 x2 : LeftInverseMagmaTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (∀ (x : LeftInverseMagmaTerm) , (P x))) 
  | plinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl x1) (inductionB plinvl x2))  
  def inductionCl   {A : Type} {P : ((ClLeftInverseMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftInverseMagmaTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (∀ (x : (ClLeftInverseMagmaTerm A)) , (P x)))) 
  | psing plinvcl (sing x1) := (psing x1)  
  | psing plinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl x1) (inductionCl psing plinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpLeftInverseMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftInverseMagmaTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (∀ (x : (OpLeftInverseMagmaTerm n)) , (P x)))) 
  | pv plinvol (v x1) := (pv x1)  
  | pv plinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol x1) (inductionOpB pv plinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLeftInverseMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftInverseMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (∀ (x : (OpLeftInverseMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 plinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 x1) (inductionOp pv2 psing2 plinvol2 x2))  
  def stageB  : (LeftInverseMagmaTerm → (Staged LeftInverseMagmaTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClLeftInverseMagmaTerm A) → (Staged (ClLeftInverseMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpLeftInverseMagmaTerm n) → (Staged (OpLeftInverseMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLeftInverseMagmaTerm2 n A) → (Staged (OpLeftInverseMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftInverseMagma