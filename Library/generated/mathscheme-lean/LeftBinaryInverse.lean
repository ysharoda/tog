import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftBinaryInverse   
  structure LeftBinaryInverse  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A)))
       (leftInverse : (∀ {x y : A} , (rinv (linv x y) x) = y)) 
  
  open LeftBinaryInverse
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftInverseP : (∀ {xP yP : (Prod A A)} , (rinvP (linvP xP yP) xP) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftBinaryInverse A1)) (Le2 : (LeftBinaryInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Le1) x1 x2)) = ((linv Le2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Le1) x1 x2)) = ((rinv Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftBinaryInverse A1)) (Le2 : (LeftBinaryInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Le1) x1 x2) ((rinv Le2) y1 y2)))))) 
  
  inductive LeftBinaryInverseTerm   : Type  
     | linvL : (LeftBinaryInverseTerm → (LeftBinaryInverseTerm → LeftBinaryInverseTerm)) 
     | rinvL : (LeftBinaryInverseTerm → (LeftBinaryInverseTerm → LeftBinaryInverseTerm))  
      open LeftBinaryInverseTerm 
  
  inductive ClLeftBinaryInverseTerm  (A : Type) : Type  
     | sing : (A → ClLeftBinaryInverseTerm) 
     | linvCl : (ClLeftBinaryInverseTerm → (ClLeftBinaryInverseTerm → ClLeftBinaryInverseTerm)) 
     | rinvCl : (ClLeftBinaryInverseTerm → (ClLeftBinaryInverseTerm → ClLeftBinaryInverseTerm))  
      open ClLeftBinaryInverseTerm 
  
  inductive OpLeftBinaryInverseTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftBinaryInverseTerm) 
     | linvOL : (OpLeftBinaryInverseTerm → (OpLeftBinaryInverseTerm → OpLeftBinaryInverseTerm)) 
     | rinvOL : (OpLeftBinaryInverseTerm → (OpLeftBinaryInverseTerm → OpLeftBinaryInverseTerm))  
      open OpLeftBinaryInverseTerm 
  
  inductive OpLeftBinaryInverseTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftBinaryInverseTerm2) 
     | sing2 : (A → OpLeftBinaryInverseTerm2) 
     | linvOL2 : (OpLeftBinaryInverseTerm2 → (OpLeftBinaryInverseTerm2 → OpLeftBinaryInverseTerm2)) 
     | rinvOL2 : (OpLeftBinaryInverseTerm2 → (OpLeftBinaryInverseTerm2 → OpLeftBinaryInverseTerm2))  
      open OpLeftBinaryInverseTerm2 
  
  def simplifyCl   {A : Type}  : ((ClLeftBinaryInverseTerm A) → (ClLeftBinaryInverseTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLeftBinaryInverseTerm n) → (OpLeftBinaryInverseTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLeftBinaryInverseTerm2 n A) → (OpLeftBinaryInverseTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftBinaryInverse A) → (LeftBinaryInverseTerm → A)) 
  | Le (linvL x1 x2) := ((linv Le) (evalB Le x1) (evalB Le x2))  
  | Le (rinvL x1 x2) := ((rinv Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftBinaryInverse A) → ((ClLeftBinaryInverseTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (linvCl x1 x2) := ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  | Le (rinvCl x1 x2) := ((rinv Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((LeftBinaryInverse A) → ((vector A n) → ((OpLeftBinaryInverseTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (linvOL x1 x2) := ((linv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  | Le vars (rinvOL x1 x2) := ((rinv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((LeftBinaryInverse A) → ((vector A n) → ((OpLeftBinaryInverseTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (linvOL2 x1 x2) := ((linv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  | Le vars (rinvOL2 x1 x2) := ((rinv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   {P : (LeftBinaryInverseTerm → Type)}  : ((∀ (x1 x2 : LeftBinaryInverseTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : LeftBinaryInverseTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : LeftBinaryInverseTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClLeftBinaryInverseTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftBinaryInverseTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClLeftBinaryInverseTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClLeftBinaryInverseTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpLeftBinaryInverseTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftBinaryInverseTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpLeftBinaryInverseTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpLeftBinaryInverseTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLeftBinaryInverseTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftBinaryInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpLeftBinaryInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpLeftBinaryInverseTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (LeftBinaryInverseTerm → (Staged LeftBinaryInverseTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClLeftBinaryInverseTerm A) → (Staged (ClLeftBinaryInverseTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpLeftBinaryInverseTerm n) → (Staged (OpLeftBinaryInverseTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLeftBinaryInverseTerm2 n A) → (Staged (OpLeftBinaryInverseTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftBinaryInverse