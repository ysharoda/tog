import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BinaryInverse   
  structure BinaryInverse  (A : Type) : Type := 
       (linv : (A → (A → A)))
       (rinv : (A → (A → A)))
       (leftInverse : (∀ {x y : A} , (rinv (linv x y) x) = y))
       (rightInverse : (∀ {x y : A} , (linv x (rinv y x)) = y)) 
  
  open BinaryInverse
  structure Sig  (AS : Type) : Type := 
       (linvS : (AS → (AS → AS)))
       (rinvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rinvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftInverseP : (∀ {xP yP : (Prod A A)} , (rinvP (linvP xP yP) xP) = yP))
       (rightInverseP : (∀ {xP yP : (Prod A A)} , (linvP xP (rinvP yP xP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bi1 : (BinaryInverse A1)) (Bi2 : (BinaryInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Bi1) x1 x2)) = ((linv Bi2) (hom x1) (hom x2))))
       (pres_rinv : (∀ {x1 x2 : A1} , (hom ((rinv Bi1) x1 x2)) = ((rinv Bi2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bi1 : (BinaryInverse A1)) (Bi2 : (BinaryInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Bi1) x1 x2) ((linv Bi2) y1 y2))))))
       (interp_rinv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((rinv Bi1) x1 x2) ((rinv Bi2) y1 y2)))))) 
  
  inductive BinaryInverseTerm   : Type  
     | linvL : (BinaryInverseTerm → (BinaryInverseTerm → BinaryInverseTerm)) 
     | rinvL : (BinaryInverseTerm → (BinaryInverseTerm → BinaryInverseTerm))  
      open BinaryInverseTerm 
  
  inductive ClBinaryInverseTerm  (A : Type) : Type  
     | sing : (A → ClBinaryInverseTerm) 
     | linvCl : (ClBinaryInverseTerm → (ClBinaryInverseTerm → ClBinaryInverseTerm)) 
     | rinvCl : (ClBinaryInverseTerm → (ClBinaryInverseTerm → ClBinaryInverseTerm))  
      open ClBinaryInverseTerm 
  
  inductive OpBinaryInverseTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBinaryInverseTerm) 
     | linvOL : (OpBinaryInverseTerm → (OpBinaryInverseTerm → OpBinaryInverseTerm)) 
     | rinvOL : (OpBinaryInverseTerm → (OpBinaryInverseTerm → OpBinaryInverseTerm))  
      open OpBinaryInverseTerm 
  
  inductive OpBinaryInverseTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBinaryInverseTerm2) 
     | sing2 : (A → OpBinaryInverseTerm2) 
     | linvOL2 : (OpBinaryInverseTerm2 → (OpBinaryInverseTerm2 → OpBinaryInverseTerm2)) 
     | rinvOL2 : (OpBinaryInverseTerm2 → (OpBinaryInverseTerm2 → OpBinaryInverseTerm2))  
      open OpBinaryInverseTerm2 
  
  def simplifyCl   (A : Type)  : ((ClBinaryInverseTerm A) → (ClBinaryInverseTerm A)) 
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (rinvCl x1 x2) := (rinvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpBinaryInverseTerm n) → (OpBinaryInverseTerm n)) 
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (rinvOL x1 x2) := (rinvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpBinaryInverseTerm2 n A) → (OpBinaryInverseTerm2 n A)) 
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (rinvOL2 x1 x2) := (rinvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BinaryInverse A) → (BinaryInverseTerm → A)) 
  | Bi (linvL x1 x2) := ((linv Bi) (evalB Bi x1) (evalB Bi x2))  
  | Bi (rinvL x1 x2) := ((rinv Bi) (evalB Bi x1) (evalB Bi x2))  
  def evalCl   {A : Type}  : ((BinaryInverse A) → ((ClBinaryInverseTerm A) → A)) 
  | Bi (sing x1) := x1  
  | Bi (linvCl x1 x2) := ((linv Bi) (evalCl Bi x1) (evalCl Bi x2))  
  | Bi (rinvCl x1 x2) := ((rinv Bi) (evalCl Bi x1) (evalCl Bi x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((BinaryInverse A) → ((vector A n) → ((OpBinaryInverseTerm n) → A))) 
  | Bi vars (v x1) := (nth vars x1)  
  | Bi vars (linvOL x1 x2) := ((linv Bi) (evalOpB Bi vars x1) (evalOpB Bi vars x2))  
  | Bi vars (rinvOL x1 x2) := ((rinv Bi) (evalOpB Bi vars x1) (evalOpB Bi vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((BinaryInverse A) → ((vector A n) → ((OpBinaryInverseTerm2 n A) → A))) 
  | Bi vars (v2 x1) := (nth vars x1)  
  | Bi vars (sing2 x1) := x1  
  | Bi vars (linvOL2 x1 x2) := ((linv Bi) (evalOp Bi vars x1) (evalOp Bi vars x2))  
  | Bi vars (rinvOL2 x1 x2) := ((rinv Bi) (evalOp Bi vars x1) (evalOp Bi vars x2))  
  def inductionB   (P : (BinaryInverseTerm → Type))  : ((∀ (x1 x2 : BinaryInverseTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → ((∀ (x1 x2 : BinaryInverseTerm) , ((P x1) → ((P x2) → (P (rinvL x1 x2))))) → (∀ (x : BinaryInverseTerm) , (P x)))) 
  | plinvl prinvl (linvL x1 x2) := (plinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  | plinvl prinvl (rinvL x1 x2) := (prinvl _ _ (inductionB plinvl prinvl x1) (inductionB plinvl prinvl x2))  
  def inductionCl   (A : Type) (P : ((ClBinaryInverseTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBinaryInverseTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → ((∀ (x1 x2 : (ClBinaryInverseTerm A)) , ((P x1) → ((P x2) → (P (rinvCl x1 x2))))) → (∀ (x : (ClBinaryInverseTerm A)) , (P x))))) 
  | psing plinvcl prinvcl (sing x1) := (psing x1)  
  | psing plinvcl prinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  | psing plinvcl prinvcl (rinvCl x1 x2) := (prinvcl _ _ (inductionCl psing plinvcl prinvcl x1) (inductionCl psing plinvcl prinvcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpBinaryInverseTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBinaryInverseTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → ((∀ (x1 x2 : (OpBinaryInverseTerm n)) , ((P x1) → ((P x2) → (P (rinvOL x1 x2))))) → (∀ (x : (OpBinaryInverseTerm n)) , (P x))))) 
  | pv plinvol prinvol (v x1) := (pv x1)  
  | pv plinvol prinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  | pv plinvol prinvol (rinvOL x1 x2) := (prinvol _ _ (inductionOpB pv plinvol prinvol x1) (inductionOpB pv plinvol prinvol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpBinaryInverseTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBinaryInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → ((∀ (x1 x2 : (OpBinaryInverseTerm2 n A)) , ((P x1) → ((P x2) → (P (rinvOL2 x1 x2))))) → (∀ (x : (OpBinaryInverseTerm2 n A)) , (P x)))))) 
  | pv2 psing2 plinvol2 prinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 plinvol2 prinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  | pv2 psing2 plinvol2 prinvol2 (rinvOL2 x1 x2) := (prinvol2 _ _ (inductionOp pv2 psing2 plinvol2 prinvol2 x1) (inductionOp pv2 psing2 plinvol2 prinvol2 x2))  
  def stageB  : (BinaryInverseTerm → (Staged BinaryInverseTerm))
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  | (rinvL x1 x2) := (stage2 rinvL (codeLift2 rinvL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClBinaryInverseTerm A) → (Staged (ClBinaryInverseTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  | (rinvCl x1 x2) := (stage2 rinvCl (codeLift2 rinvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpBinaryInverseTerm n) → (Staged (OpBinaryInverseTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  | (rinvOL x1 x2) := (stage2 rinvOL (codeLift2 rinvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpBinaryInverseTerm2 n A) → (Staged (OpBinaryInverseTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  | (rinvOL2 x1 x2) := (stage2 rinvOL2 (codeLift2 rinvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (linvT : ((Repr A) → ((Repr A) → (Repr A))))
       (rinvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end BinaryInverse