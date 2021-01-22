import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightBinaryInverse   
  structure RightBinaryInverse  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A)))
       (rightInverse : (∀ {x y : A} , (linv x (rinv y x)) = y)) 
  
  open RightBinaryInverse
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightInverseP : (∀ {xP yP : (Prod A A)} , (linvP xP (rinvP yP xP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightBinaryInverse A1)) (Ri2 : (RightBinaryInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Ri1) x1 x2)) = ((linv Ri2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Ri1) x1 x2)) = ((rinv Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightBinaryInverse A1)) (Ri2 : (RightBinaryInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Ri1) x1 x2) ((linv Ri2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Ri1) x1 x2) ((rinv Ri2) y1 y2)))))) 
  
  inductive RightBinaryInverseTerm   : Type  
     | linvL : (RightBinaryInverseTerm → (RightBinaryInverseTerm → RightBinaryInverseTerm)) 
     | rinvL : (RightBinaryInverseTerm → (RightBinaryInverseTerm → RightBinaryInverseTerm))  
      open RightBinaryInverseTerm 
  
  inductive ClRightBinaryInverseTerm  (A : Type) : Type  
     | sing : (A → ClRightBinaryInverseTerm) 
     | linvCl : (ClRightBinaryInverseTerm → (ClRightBinaryInverseTerm → ClRightBinaryInverseTerm)) 
     | rinvCl : (ClRightBinaryInverseTerm → (ClRightBinaryInverseTerm → ClRightBinaryInverseTerm))  
      open ClRightBinaryInverseTerm 
  
  inductive OpRightBinaryInverseTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightBinaryInverseTerm) 
     | linvOL : (OpRightBinaryInverseTerm → (OpRightBinaryInverseTerm → OpRightBinaryInverseTerm)) 
     | rinvOL : (OpRightBinaryInverseTerm → (OpRightBinaryInverseTerm → OpRightBinaryInverseTerm))  
      open OpRightBinaryInverseTerm 
  
  inductive OpRightBinaryInverseTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightBinaryInverseTerm2) 
     | sing2 : (A → OpRightBinaryInverseTerm2) 
     | linvOL2 : (OpRightBinaryInverseTerm2 → (OpRightBinaryInverseTerm2 → OpRightBinaryInverseTerm2)) 
     | rinvOL2 : (OpRightBinaryInverseTerm2 → (OpRightBinaryInverseTerm2 → OpRightBinaryInverseTerm2))  
      open OpRightBinaryInverseTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightBinaryInverseTerm A) → (ClRightBinaryInverseTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightBinaryInverseTerm n) → (OpRightBinaryInverseTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightBinaryInverseTerm2 n A) → (OpRightBinaryInverseTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightBinaryInverse A) → (RightBinaryInverseTerm → A)) 
  | Ri (linvL x1 x2) := ((linv Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (rinvL x1 x2) := ((rinv Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightBinaryInverse A) → ((ClRightBinaryInverseTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (linvCl x1 x2) := ((linv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (rinvCl x1 x2) := ((rinv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightBinaryInverse A) → ((vector A n) → ((OpRightBinaryInverseTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (linvOL x1 x2) := ((linv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (rinvOL x1 x2) := ((rinv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightBinaryInverse A) → ((vector A n) → ((OpRightBinaryInverseTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (linvOL2 x1 x2) := ((linv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (rinvOL2 x1 x2) := ((rinv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightBinaryInverseTerm → Type)}  : ((∀ (x1 x2 : RightBinaryInverseTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : RightBinaryInverseTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : RightBinaryInverseTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRightBinaryInverseTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightBinaryInverseTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClRightBinaryInverseTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClRightBinaryInverseTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightBinaryInverseTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightBinaryInverseTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpRightBinaryInverseTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpRightBinaryInverseTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightBinaryInverseTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightBinaryInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRightBinaryInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpRightBinaryInverseTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (RightBinaryInverseTerm → (Staged RightBinaryInverseTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightBinaryInverseTerm A) → (Staged (ClRightBinaryInverseTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightBinaryInverseTerm n) → (Staged (OpRightBinaryInverseTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightBinaryInverseTerm2 n A) → (Staged (OpRightBinaryInverseTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightBinaryInverse