import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightSelfInverse   
  structure RightSelfInverse  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rightSelfInverse_linv : (∀ {x y : A} , (linv (linv x y) y) = x)) 
  
  open RightSelfInverse
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightSelfInverse_linvP : (∀ {xP yP : (Prod A A)} , (linvP (linvP xP yP) yP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightSelfInverse A1)) (Ri2 : (RightSelfInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Ri1) x1 x2)) = ((linv Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightSelfInverse A1)) (Ri2 : (RightSelfInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Ri1) x1 x2) ((linv Ri2) y1 y2)))))) 
  
  inductive RightSelfInverseTerm   : Type  
     | linvL : (RightSelfInverseTerm → (RightSelfInverseTerm → RightSelfInverseTerm))  
      open RightSelfInverseTerm 
  
  inductive ClRightSelfInverseTerm  (A : Type) : Type  
     | sing : (A → ClRightSelfInverseTerm) 
     | linvCl : (ClRightSelfInverseTerm → (ClRightSelfInverseTerm → ClRightSelfInverseTerm))  
      open ClRightSelfInverseTerm 
  
  inductive OpRightSelfInverseTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightSelfInverseTerm) 
     | linvOL : (OpRightSelfInverseTerm → (OpRightSelfInverseTerm → OpRightSelfInverseTerm))  
      open OpRightSelfInverseTerm 
  
  inductive OpRightSelfInverseTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightSelfInverseTerm2) 
     | sing2 : (A → OpRightSelfInverseTerm2) 
     | linvOL2 : (OpRightSelfInverseTerm2 → (OpRightSelfInverseTerm2 → OpRightSelfInverseTerm2))  
      open OpRightSelfInverseTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightSelfInverseTerm A) → (ClRightSelfInverseTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightSelfInverseTerm n) → (OpRightSelfInverseTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightSelfInverseTerm2 n A) → (OpRightSelfInverseTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightSelfInverse A) → (RightSelfInverseTerm → A)) 
  | Ri (linvL x1 x2) := ((linv Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightSelfInverse A) → ((ClRightSelfInverseTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (linvCl x1 x2) := ((linv Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightSelfInverse A) → ((vector A n) → ((OpRightSelfInverseTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (linvOL x1 x2) := ((linv Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightSelfInverse A) → ((vector A n) → ((OpRightSelfInverseTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (linvOL2 x1 x2) := ((linv Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightSelfInverseTerm → Type)}  : ((∀ (x1 x2 : RightSelfInverseTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (∀ (x : RightSelfInverseTerm) , (P x))) 
  | plinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl x1) (inductionB plinvl x2))  
  def inductionCl   {A : Type} {P : ((ClRightSelfInverseTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightSelfInverseTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (∀ (x : (ClRightSelfInverseTerm A)) , (P x)))) 
  | psing plinvcl (sing x1) := (psing x1)  
  | psing plinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl x1) (inductionCl psing plinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightSelfInverseTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightSelfInverseTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (∀ (x : (OpRightSelfInverseTerm n)) , (P x)))) 
  | pv plinvol (v x1) := (pv x1)  
  | pv plinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol x1) (inductionOpB pv plinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightSelfInverseTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightSelfInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (∀ (x : (OpRightSelfInverseTerm2 n A)) , (P x))))) 
  | pv2 psing2 plinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 x1) (inductionOp pv2 psing2 plinvol2 x2))  
  def stageB  : (RightSelfInverseTerm → (Staged RightSelfInverseTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightSelfInverseTerm A) → (Staged (ClRightSelfInverseTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightSelfInverseTerm n) → (Staged (OpRightSelfInverseTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightSelfInverseTerm2 n A) → (Staged (OpRightSelfInverseTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightSelfInverse