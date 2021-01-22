import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveMagmaSig   
  structure InvolutiveMagmaSig  (A : Type) : Type := 
       (prim : (A → A))
       (op : (A → (A → A))) 
  
  open InvolutiveMagmaSig
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveMagmaSig A1)) (In2 : (InvolutiveMagmaSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op In1) x1 x2)) = ((op In2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveMagmaSig A1)) (In2 : (InvolutiveMagmaSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2)))))) 
  
  inductive InvolutiveMagmaSigTerm   : Type  
     | primL : (InvolutiveMagmaSigTerm → InvolutiveMagmaSigTerm) 
     | opL : (InvolutiveMagmaSigTerm → (InvolutiveMagmaSigTerm → InvolutiveMagmaSigTerm))  
      open InvolutiveMagmaSigTerm 
  
  inductive ClInvolutiveMagmaSigTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveMagmaSigTerm) 
     | primCl : (ClInvolutiveMagmaSigTerm → ClInvolutiveMagmaSigTerm) 
     | opCl : (ClInvolutiveMagmaSigTerm → (ClInvolutiveMagmaSigTerm → ClInvolutiveMagmaSigTerm))  
      open ClInvolutiveMagmaSigTerm 
  
  inductive OpInvolutiveMagmaSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveMagmaSigTerm) 
     | primOL : (OpInvolutiveMagmaSigTerm → OpInvolutiveMagmaSigTerm) 
     | opOL : (OpInvolutiveMagmaSigTerm → (OpInvolutiveMagmaSigTerm → OpInvolutiveMagmaSigTerm))  
      open OpInvolutiveMagmaSigTerm 
  
  inductive OpInvolutiveMagmaSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveMagmaSigTerm2) 
     | sing2 : (A → OpInvolutiveMagmaSigTerm2) 
     | primOL2 : (OpInvolutiveMagmaSigTerm2 → OpInvolutiveMagmaSigTerm2) 
     | opOL2 : (OpInvolutiveMagmaSigTerm2 → (OpInvolutiveMagmaSigTerm2 → OpInvolutiveMagmaSigTerm2))  
      open OpInvolutiveMagmaSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInvolutiveMagmaSigTerm A) → (ClInvolutiveMagmaSigTerm A)) 
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInvolutiveMagmaSigTerm n) → (OpInvolutiveMagmaSigTerm n)) 
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInvolutiveMagmaSigTerm2 n A) → (OpInvolutiveMagmaSigTerm2 n A)) 
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveMagmaSig A) → (InvolutiveMagmaSigTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In (opL x1 x2) := ((op In) (evalB In x1) (evalB In x2))  
  def evalCl   {A : Type}  : ((InvolutiveMagmaSig A) → ((ClInvolutiveMagmaSigTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In (opCl x1 x2) := ((op In) (evalCl In x1) (evalCl In x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InvolutiveMagmaSig A) → ((vector A n) → ((OpInvolutiveMagmaSigTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars (opOL x1 x2) := ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((InvolutiveMagmaSig A) → ((vector A n) → ((OpInvolutiveMagmaSigTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars (opOL2 x1 x2) := ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  def inductionB   {P : (InvolutiveMagmaSigTerm → Type)}  : ((∀ (x1 : InvolutiveMagmaSigTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : InvolutiveMagmaSigTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : InvolutiveMagmaSigTerm) , (P x)))) 
  | ppriml popl (primL x1) := (ppriml _ (inductionB ppriml popl x1))  
  | ppriml popl (opL x1 x2) := (popl _ _ (inductionB ppriml popl x1) (inductionB ppriml popl x2))  
  def inductionCl   {A : Type} {P : ((ClInvolutiveMagmaSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutiveMagmaSigTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClInvolutiveMagmaSigTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClInvolutiveMagmaSigTerm A)) , (P x))))) 
  | psing pprimcl popcl (sing x1) := (psing x1)  
  | psing pprimcl popcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl popcl x1))  
  | psing pprimcl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pprimcl popcl x1) (inductionCl psing pprimcl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpInvolutiveMagmaSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutiveMagmaSigTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpInvolutiveMagmaSigTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpInvolutiveMagmaSigTerm n)) , (P x))))) 
  | pv pprimol popol (v x1) := (pv x1)  
  | pv pprimol popol (primOL x1) := (pprimol _ (inductionOpB pv pprimol popol x1))  
  | pv pprimol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pprimol popol x1) (inductionOpB pv pprimol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInvolutiveMagmaSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutiveMagmaSigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpInvolutiveMagmaSigTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpInvolutiveMagmaSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 popol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 popol2 x1))  
  | pv2 psing2 pprimol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pprimol2 popol2 x1) (inductionOp pv2 psing2 pprimol2 popol2 x2))  
  def stageB  : (InvolutiveMagmaSigTerm → (Staged InvolutiveMagmaSigTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClInvolutiveMagmaSigTerm A) → (Staged (ClInvolutiveMagmaSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpInvolutiveMagmaSigTerm n) → (Staged (OpInvolutiveMagmaSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInvolutiveMagmaSigTerm2 n A) → (Staged (OpInvolutiveMagmaSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end InvolutiveMagmaSig