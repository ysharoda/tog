import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftSpindle_ShelfSig   
  structure LeftSpindle_ShelfSig  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (leftDistributive : (∀ {x y z : A} , (linv x (linv y z)) = (linv (linv x y) (linv x z))))
       (idempotent_linv : (∀ {x : A} , (linv x x) = x))
       (rinv : (A → (A → A))) 
  
  open LeftSpindle_ShelfSig
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftDistributiveP : (∀ {xP yP zP : (Prod A A)} , (linvP xP (linvP yP zP)) = (linvP (linvP xP yP) (linvP xP zP))))
       (idempotent_linvP : (∀ {xP : (Prod A A)} , (linvP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftSpindle_ShelfSig A1)) (Le2 : (LeftSpindle_ShelfSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Le1) x1 x2)) = ((linv Le2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Le1) x1 x2)) = ((rinv Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftSpindle_ShelfSig A1)) (Le2 : (LeftSpindle_ShelfSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Le1) x1 x2) ((rinv Le2) y1 y2)))))) 
  
  inductive LeftSpindle_ShelfSigTerm   : Type  
     | linvL : (LeftSpindle_ShelfSigTerm → (LeftSpindle_ShelfSigTerm → LeftSpindle_ShelfSigTerm)) 
     | rinvL : (LeftSpindle_ShelfSigTerm → (LeftSpindle_ShelfSigTerm → LeftSpindle_ShelfSigTerm))  
      open LeftSpindle_ShelfSigTerm 
  
  inductive ClLeftSpindle_ShelfSigTerm  (A : Type) : Type  
     | sing : (A → ClLeftSpindle_ShelfSigTerm) 
     | linvCl : (ClLeftSpindle_ShelfSigTerm → (ClLeftSpindle_ShelfSigTerm → ClLeftSpindle_ShelfSigTerm)) 
     | rinvCl : (ClLeftSpindle_ShelfSigTerm → (ClLeftSpindle_ShelfSigTerm → ClLeftSpindle_ShelfSigTerm))  
      open ClLeftSpindle_ShelfSigTerm 
  
  inductive OpLeftSpindle_ShelfSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftSpindle_ShelfSigTerm) 
     | linvOL : (OpLeftSpindle_ShelfSigTerm → (OpLeftSpindle_ShelfSigTerm → OpLeftSpindle_ShelfSigTerm)) 
     | rinvOL : (OpLeftSpindle_ShelfSigTerm → (OpLeftSpindle_ShelfSigTerm → OpLeftSpindle_ShelfSigTerm))  
      open OpLeftSpindle_ShelfSigTerm 
  
  inductive OpLeftSpindle_ShelfSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftSpindle_ShelfSigTerm2) 
     | sing2 : (A → OpLeftSpindle_ShelfSigTerm2) 
     | linvOL2 : (OpLeftSpindle_ShelfSigTerm2 → (OpLeftSpindle_ShelfSigTerm2 → OpLeftSpindle_ShelfSigTerm2)) 
     | rinvOL2 : (OpLeftSpindle_ShelfSigTerm2 → (OpLeftSpindle_ShelfSigTerm2 → OpLeftSpindle_ShelfSigTerm2))  
      open OpLeftSpindle_ShelfSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClLeftSpindle_ShelfSigTerm A) → (ClLeftSpindle_ShelfSigTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLeftSpindle_ShelfSigTerm n) → (OpLeftSpindle_ShelfSigTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLeftSpindle_ShelfSigTerm2 n A) → (OpLeftSpindle_ShelfSigTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftSpindle_ShelfSig A) → (LeftSpindle_ShelfSigTerm → A)) 
  | Le (linvL x1 x2) := ((linv Le) (evalB Le x1) (evalB Le x2))  
  | Le (rinvL x1 x2) := ((rinv Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftSpindle_ShelfSig A) → ((ClLeftSpindle_ShelfSigTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (linvCl x1 x2) := ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  | Le (rinvCl x1 x2) := ((rinv Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((LeftSpindle_ShelfSig A) → ((vector A n) → ((OpLeftSpindle_ShelfSigTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (linvOL x1 x2) := ((linv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  | Le vars (rinvOL x1 x2) := ((rinv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((LeftSpindle_ShelfSig A) → ((vector A n) → ((OpLeftSpindle_ShelfSigTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (linvOL2 x1 x2) := ((linv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  | Le vars (rinvOL2 x1 x2) := ((rinv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   {P : (LeftSpindle_ShelfSigTerm → Type)}  : ((∀ (x1 x2 : LeftSpindle_ShelfSigTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : LeftSpindle_ShelfSigTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : LeftSpindle_ShelfSigTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClLeftSpindle_ShelfSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftSpindle_ShelfSigTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClLeftSpindle_ShelfSigTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClLeftSpindle_ShelfSigTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpLeftSpindle_ShelfSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftSpindle_ShelfSigTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpLeftSpindle_ShelfSigTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpLeftSpindle_ShelfSigTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLeftSpindle_ShelfSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftSpindle_ShelfSigTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpLeftSpindle_ShelfSigTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpLeftSpindle_ShelfSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (LeftSpindle_ShelfSigTerm → (Staged LeftSpindle_ShelfSigTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClLeftSpindle_ShelfSigTerm A) → (Staged (ClLeftSpindle_ShelfSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpLeftSpindle_ShelfSigTerm n) → (Staged (OpLeftSpindle_ShelfSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLeftSpindle_ShelfSigTerm2 n A) → (Staged (OpLeftSpindle_ShelfSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftSpindle_ShelfSig