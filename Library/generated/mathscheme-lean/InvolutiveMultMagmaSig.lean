import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveMultMagmaSig   
  structure InvolutiveMultMagmaSig  (A : Type) : Type := 
       (times : (A → (A → A)))
       (prim : (A → A)) 
  
  open InvolutiveMultMagmaSig
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveMultMagmaSig A1)) (In2 : (InvolutiveMultMagmaSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times In1) x1 x2)) = ((times In2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveMultMagmaSig A1)) (In2 : (InvolutiveMultMagmaSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times In1) x1 x2) ((times In2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutiveMultMagmaSigTerm   : Type  
     | timesL : (InvolutiveMultMagmaSigTerm → (InvolutiveMultMagmaSigTerm → InvolutiveMultMagmaSigTerm)) 
     | primL : (InvolutiveMultMagmaSigTerm → InvolutiveMultMagmaSigTerm)  
      open InvolutiveMultMagmaSigTerm 
  
  inductive ClInvolutiveMultMagmaSigTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveMultMagmaSigTerm) 
     | timesCl : (ClInvolutiveMultMagmaSigTerm → (ClInvolutiveMultMagmaSigTerm → ClInvolutiveMultMagmaSigTerm)) 
     | primCl : (ClInvolutiveMultMagmaSigTerm → ClInvolutiveMultMagmaSigTerm)  
      open ClInvolutiveMultMagmaSigTerm 
  
  inductive OpInvolutiveMultMagmaSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveMultMagmaSigTerm) 
     | timesOL : (OpInvolutiveMultMagmaSigTerm → (OpInvolutiveMultMagmaSigTerm → OpInvolutiveMultMagmaSigTerm)) 
     | primOL : (OpInvolutiveMultMagmaSigTerm → OpInvolutiveMultMagmaSigTerm)  
      open OpInvolutiveMultMagmaSigTerm 
  
  inductive OpInvolutiveMultMagmaSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveMultMagmaSigTerm2) 
     | sing2 : (A → OpInvolutiveMultMagmaSigTerm2) 
     | timesOL2 : (OpInvolutiveMultMagmaSigTerm2 → (OpInvolutiveMultMagmaSigTerm2 → OpInvolutiveMultMagmaSigTerm2)) 
     | primOL2 : (OpInvolutiveMultMagmaSigTerm2 → OpInvolutiveMultMagmaSigTerm2)  
      open OpInvolutiveMultMagmaSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInvolutiveMultMagmaSigTerm A) → (ClInvolutiveMultMagmaSigTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInvolutiveMultMagmaSigTerm n) → (OpInvolutiveMultMagmaSigTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInvolutiveMultMagmaSigTerm2 n A) → (OpInvolutiveMultMagmaSigTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveMultMagmaSig A) → (InvolutiveMultMagmaSigTerm → A)) 
  | In (timesL x1 x2) := ((times In) (evalB In x1) (evalB In x2))  
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutiveMultMagmaSig A) → ((ClInvolutiveMultMagmaSigTerm A) → A)) 
  | In (sing x1) := x1  
  | In (timesCl x1 x2) := ((times In) (evalCl In x1) (evalCl In x2))  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InvolutiveMultMagmaSig A) → ((vector A n) → ((OpInvolutiveMultMagmaSigTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (timesOL x1 x2) := ((times In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((InvolutiveMultMagmaSig A) → ((vector A n) → ((OpInvolutiveMultMagmaSigTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (timesOL2 x1 x2) := ((times In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   {P : (InvolutiveMultMagmaSigTerm → Type)}  : ((∀ (x1 x2 : InvolutiveMultMagmaSigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 : InvolutiveMultMagmaSigTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutiveMultMagmaSigTerm) , (P x)))) 
  | ptimesl ppriml (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl ppriml x1) (inductionB ptimesl ppriml x2))  
  | ptimesl ppriml (primL x1) := (ppriml _ (inductionB ptimesl ppriml x1))  
  def inductionCl   {A : Type} {P : ((ClInvolutiveMultMagmaSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClInvolutiveMultMagmaSigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 : (ClInvolutiveMultMagmaSigTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutiveMultMagmaSigTerm A)) , (P x))))) 
  | psing ptimescl pprimcl (sing x1) := (psing x1)  
  | psing ptimescl pprimcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl pprimcl x1) (inductionCl psing ptimescl pprimcl x2))  
  | psing ptimescl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl pprimcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpInvolutiveMultMagmaSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpInvolutiveMultMagmaSigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 : (OpInvolutiveMultMagmaSigTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutiveMultMagmaSigTerm n)) , (P x))))) 
  | pv ptimesol pprimol (v x1) := (pv x1)  
  | pv ptimesol pprimol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pprimol x1) (inductionOpB pv ptimesol pprimol x2))  
  | pv ptimesol pprimol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pprimol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInvolutiveMultMagmaSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpInvolutiveMultMagmaSigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 : (OpInvolutiveMultMagmaSigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutiveMultMagmaSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pprimol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pprimol2 x1) (inductionOp pv2 psing2 ptimesol2 pprimol2 x2))  
  | pv2 psing2 ptimesol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pprimol2 x1))  
  def stageB  : (InvolutiveMultMagmaSigTerm → (Staged InvolutiveMultMagmaSigTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClInvolutiveMultMagmaSigTerm A) → (Staged (ClInvolutiveMultMagmaSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpInvolutiveMultMagmaSigTerm n) → (Staged (OpInvolutiveMultMagmaSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInvolutiveMultMagmaSigTerm2 n A) → (Staged (OpInvolutiveMultMagmaSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end InvolutiveMultMagmaSig