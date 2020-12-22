import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutivePointedMagmaSig   
  structure InvolutivePointedMagmaSig  (A : Type) : Type := 
       (prim : (A → A))
       (e : A)
       (op : (A → (A → A))) 
  
  open InvolutivePointedMagmaSig
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutivePointedMagmaSig A1)) (In2 : (InvolutivePointedMagmaSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_e : (hom (e In1)) = (e In2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op In1) x1 x2)) = ((op In2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutivePointedMagmaSig A1)) (In2 : (InvolutivePointedMagmaSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_e : (interp (e In1) (e In2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2)))))) 
  
  inductive InvolutivePointedMagmaSigTerm   : Type  
     | primL : (InvolutivePointedMagmaSigTerm → InvolutivePointedMagmaSigTerm) 
     | eL : InvolutivePointedMagmaSigTerm 
     | opL : (InvolutivePointedMagmaSigTerm → (InvolutivePointedMagmaSigTerm → InvolutivePointedMagmaSigTerm))  
      open InvolutivePointedMagmaSigTerm 
  
  inductive ClInvolutivePointedMagmaSigTerm  (A : Type) : Type  
     | sing : (A → ClInvolutivePointedMagmaSigTerm) 
     | primCl : (ClInvolutivePointedMagmaSigTerm → ClInvolutivePointedMagmaSigTerm) 
     | eCl : ClInvolutivePointedMagmaSigTerm 
     | opCl : (ClInvolutivePointedMagmaSigTerm → (ClInvolutivePointedMagmaSigTerm → ClInvolutivePointedMagmaSigTerm))  
      open ClInvolutivePointedMagmaSigTerm 
  
  inductive OpInvolutivePointedMagmaSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutivePointedMagmaSigTerm) 
     | primOL : (OpInvolutivePointedMagmaSigTerm → OpInvolutivePointedMagmaSigTerm) 
     | eOL : OpInvolutivePointedMagmaSigTerm 
     | opOL : (OpInvolutivePointedMagmaSigTerm → (OpInvolutivePointedMagmaSigTerm → OpInvolutivePointedMagmaSigTerm))  
      open OpInvolutivePointedMagmaSigTerm 
  
  inductive OpInvolutivePointedMagmaSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutivePointedMagmaSigTerm2) 
     | sing2 : (A → OpInvolutivePointedMagmaSigTerm2) 
     | primOL2 : (OpInvolutivePointedMagmaSigTerm2 → OpInvolutivePointedMagmaSigTerm2) 
     | eOL2 : OpInvolutivePointedMagmaSigTerm2 
     | opOL2 : (OpInvolutivePointedMagmaSigTerm2 → (OpInvolutivePointedMagmaSigTerm2 → OpInvolutivePointedMagmaSigTerm2))  
      open OpInvolutivePointedMagmaSigTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutivePointedMagmaSigTerm A) → (ClInvolutivePointedMagmaSigTerm A)) 
  | (primCl x1) := (primCl (simplifyCl x1))  
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutivePointedMagmaSigTerm n) → (OpInvolutivePointedMagmaSigTerm n)) 
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutivePointedMagmaSigTerm2 n A) → (OpInvolutivePointedMagmaSigTerm2 n A)) 
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutivePointedMagmaSig A) → (InvolutivePointedMagmaSigTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In eL := (e In)  
  | In (opL x1 x2) := ((op In) (evalB In x1) (evalB In x2))  
  def evalCl   {A : Type}  : ((InvolutivePointedMagmaSig A) → ((ClInvolutivePointedMagmaSigTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In eCl := (e In)  
  | In (opCl x1 x2) := ((op In) (evalCl In x1) (evalCl In x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutivePointedMagmaSig A) → ((vector A n) → ((OpInvolutivePointedMagmaSigTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars eOL := (e In)  
  | In vars (opOL x1 x2) := ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutivePointedMagmaSig A) → ((vector A n) → ((OpInvolutivePointedMagmaSigTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars eOL2 := (e In)  
  | In vars (opOL2 x1 x2) := ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  def inductionB   (P : (InvolutivePointedMagmaSigTerm → Type))  : ((∀ (x1 : InvolutivePointedMagmaSigTerm) , ((P x1) → (P (primL x1)))) → ((P eL) → ((∀ (x1 x2 : InvolutivePointedMagmaSigTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : InvolutivePointedMagmaSigTerm) , (P x))))) 
  | ppriml pel popl (primL x1) := (ppriml _ (inductionB ppriml pel popl x1))  
  | ppriml pel popl eL := pel  
  | ppriml pel popl (opL x1 x2) := (popl _ _ (inductionB ppriml pel popl x1) (inductionB ppriml pel popl x2))  
  def inductionCl   (A : Type) (P : ((ClInvolutivePointedMagmaSigTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutivePointedMagmaSigTerm A)) , ((P x1) → (P (primCl x1)))) → ((P eCl) → ((∀ (x1 x2 : (ClInvolutivePointedMagmaSigTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClInvolutivePointedMagmaSigTerm A)) , (P x)))))) 
  | psing pprimcl pecl popcl (sing x1) := (psing x1)  
  | psing pprimcl pecl popcl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl pecl popcl x1))  
  | psing pprimcl pecl popcl eCl := pecl  
  | psing pprimcl pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pprimcl pecl popcl x1) (inductionCl psing pprimcl pecl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutivePointedMagmaSigTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutivePointedMagmaSigTerm n)) , ((P x1) → (P (primOL x1)))) → ((P eOL) → ((∀ (x1 x2 : (OpInvolutivePointedMagmaSigTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpInvolutivePointedMagmaSigTerm n)) , (P x)))))) 
  | pv pprimol peol popol (v x1) := (pv x1)  
  | pv pprimol peol popol (primOL x1) := (pprimol _ (inductionOpB pv pprimol peol popol x1))  
  | pv pprimol peol popol eOL := peol  
  | pv pprimol peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pprimol peol popol x1) (inductionOpB pv pprimol peol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutivePointedMagmaSigTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutivePointedMagmaSigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P eOL2) → ((∀ (x1 x2 : (OpInvolutivePointedMagmaSigTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpInvolutivePointedMagmaSigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pprimol2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 peol2 popol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 peol2 popol2 x1))  
  | pv2 psing2 pprimol2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 pprimol2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pprimol2 peol2 popol2 x1) (inductionOp pv2 psing2 pprimol2 peol2 popol2 x2))  
  def stageB  : (InvolutivePointedMagmaSigTerm → (Staged InvolutivePointedMagmaSigTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClInvolutivePointedMagmaSigTerm A) → (Staged (ClInvolutivePointedMagmaSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpInvolutivePointedMagmaSigTerm n) → (Staged (OpInvolutivePointedMagmaSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutivePointedMagmaSigTerm2 n A) → (Staged (OpInvolutivePointedMagmaSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end InvolutivePointedMagmaSig