import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveMagma   
  structure InvolutiveMagma  (A : Type) : Type := 
       (prim : (A → A))
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x))
       (op : (A → (A → A)))
       (antidis_prim_op : (∀ {x y : A} , (prim (op x y)) = (op (prim y) (prim x)))) 
  
  open InvolutiveMagma
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP))
       (antidis_prim_opP : (∀ {xP yP : (Prod A A)} , (primP (opP xP yP)) = (opP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveMagma A1)) (In2 : (InvolutiveMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op In1) x1 x2)) = ((op In2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveMagma A1)) (In2 : (InvolutiveMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2)))))) 
  
  inductive InvolutiveMagmaTerm   : Type  
     | primL : (InvolutiveMagmaTerm → InvolutiveMagmaTerm) 
     | opL : (InvolutiveMagmaTerm → (InvolutiveMagmaTerm → InvolutiveMagmaTerm))  
      open InvolutiveMagmaTerm 
  
  inductive ClInvolutiveMagmaTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveMagmaTerm) 
     | primCl : (ClInvolutiveMagmaTerm → ClInvolutiveMagmaTerm) 
     | opCl : (ClInvolutiveMagmaTerm → (ClInvolutiveMagmaTerm → ClInvolutiveMagmaTerm))  
      open ClInvolutiveMagmaTerm 
  
  inductive OpInvolutiveMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveMagmaTerm) 
     | primOL : (OpInvolutiveMagmaTerm → OpInvolutiveMagmaTerm) 
     | opOL : (OpInvolutiveMagmaTerm → (OpInvolutiveMagmaTerm → OpInvolutiveMagmaTerm))  
      open OpInvolutiveMagmaTerm 
  
  inductive OpInvolutiveMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveMagmaTerm2) 
     | sing2 : (A → OpInvolutiveMagmaTerm2) 
     | primOL2 : (OpInvolutiveMagmaTerm2 → OpInvolutiveMagmaTerm2) 
     | opOL2 : (OpInvolutiveMagmaTerm2 → (OpInvolutiveMagmaTerm2 → OpInvolutiveMagmaTerm2))  
      open OpInvolutiveMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInvolutiveMagmaTerm A) → (ClInvolutiveMagmaTerm A)) 
  | (primCl (primCl x)) := x  
  | (opCl (primCl y) (primCl x)) := (primCl (opCl x y))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInvolutiveMagmaTerm n) → (OpInvolutiveMagmaTerm n)) 
  | (primOL (primOL x)) := x  
  | (opOL (primOL y) (primOL x)) := (primOL (opOL x y))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInvolutiveMagmaTerm2 n A) → (OpInvolutiveMagmaTerm2 n A)) 
  | (primOL2 (primOL2 x)) := x  
  | (opOL2 (primOL2 y) (primOL2 x)) := (primOL2 (opOL2 x y))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveMagma A) → (InvolutiveMagmaTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In (opL x1 x2) := ((op In) (evalB In x1) (evalB In x2))  
  def evalCl   {A : Type}  : ((InvolutiveMagma A) → ((ClInvolutiveMagmaTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In (opCl x1 x2) := ((op In) (evalCl In x1) (evalCl In x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InvolutiveMagma A) → ((vector A n) → ((OpInvolutiveMagmaTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars (opOL x1 x2) := ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((InvolutiveMagma A) → ((vector A n) → ((OpInvolutiveMagmaTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars (opOL2 x1 x2) := ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  def inductionB   {P : (InvolutiveMagmaTerm → Type)}  : ((∀ (x1 : InvolutiveMagmaTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : InvolutiveMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : InvolutiveMagmaTerm) , (P x)))) 
  | ppriml popl (primL x1) := (ppriml _ (inductionB ppriml popl x1))  
  | ppriml popl (opL x1 x2) := (popl _ _ (inductionB ppriml popl x1) (inductionB ppriml popl x2))  
  def inductionCl   {A : Type} {P : ((ClInvolutiveMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutiveMagmaTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClInvolutiveMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClInvolutiveMagmaTerm A)) , (P x))))) 
  | psing pprimcl popcl (sing x1) := (psing x1)  
  | psing pprimcl popcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl popcl x1))  
  | psing pprimcl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pprimcl popcl x1) (inductionCl psing pprimcl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpInvolutiveMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutiveMagmaTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpInvolutiveMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpInvolutiveMagmaTerm n)) , (P x))))) 
  | pv pprimol popol (v x1) := (pv x1)  
  | pv pprimol popol (primOL x1) := (pprimol _ (inductionOpB pv pprimol popol x1))  
  | pv pprimol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pprimol popol x1) (inductionOpB pv pprimol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInvolutiveMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutiveMagmaTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpInvolutiveMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpInvolutiveMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 popol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 popol2 x1))  
  | pv2 psing2 pprimol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pprimol2 popol2 x1) (inductionOp pv2 psing2 pprimol2 popol2 x2))  
  def stageB  : (InvolutiveMagmaTerm → (Staged InvolutiveMagmaTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClInvolutiveMagmaTerm A) → (Staged (ClInvolutiveMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpInvolutiveMagmaTerm n) → (Staged (OpInvolutiveMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInvolutiveMagmaTerm2 n A) → (Staged (OpInvolutiveMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end InvolutiveMagma