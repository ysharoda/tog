import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveAddMagmaSig   
  structure InvolutiveAddMagmaSig  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (prim : (A → A)) 
  
  open InvolutiveAddMagmaSig
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (primP : ((Prod A A) → (Prod A A))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveAddMagmaSig A1)) (In2 : (InvolutiveAddMagmaSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus In1) x1 x2)) = ((plus In2) (hom x1) (hom x2))))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveAddMagmaSig A1)) (In2 : (InvolutiveAddMagmaSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus In1) x1 x2) ((plus In2) y1 y2))))))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutiveAddMagmaSigTerm   : Type  
     | plusL : (InvolutiveAddMagmaSigTerm → (InvolutiveAddMagmaSigTerm → InvolutiveAddMagmaSigTerm)) 
     | primL : (InvolutiveAddMagmaSigTerm → InvolutiveAddMagmaSigTerm)  
      open InvolutiveAddMagmaSigTerm 
  
  inductive ClInvolutiveAddMagmaSigTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveAddMagmaSigTerm) 
     | plusCl : (ClInvolutiveAddMagmaSigTerm → (ClInvolutiveAddMagmaSigTerm → ClInvolutiveAddMagmaSigTerm)) 
     | primCl : (ClInvolutiveAddMagmaSigTerm → ClInvolutiveAddMagmaSigTerm)  
      open ClInvolutiveAddMagmaSigTerm 
  
  inductive OpInvolutiveAddMagmaSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveAddMagmaSigTerm) 
     | plusOL : (OpInvolutiveAddMagmaSigTerm → (OpInvolutiveAddMagmaSigTerm → OpInvolutiveAddMagmaSigTerm)) 
     | primOL : (OpInvolutiveAddMagmaSigTerm → OpInvolutiveAddMagmaSigTerm)  
      open OpInvolutiveAddMagmaSigTerm 
  
  inductive OpInvolutiveAddMagmaSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveAddMagmaSigTerm2) 
     | sing2 : (A → OpInvolutiveAddMagmaSigTerm2) 
     | plusOL2 : (OpInvolutiveAddMagmaSigTerm2 → (OpInvolutiveAddMagmaSigTerm2 → OpInvolutiveAddMagmaSigTerm2)) 
     | primOL2 : (OpInvolutiveAddMagmaSigTerm2 → OpInvolutiveAddMagmaSigTerm2)  
      open OpInvolutiveAddMagmaSigTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutiveAddMagmaSigTerm A) → (ClInvolutiveAddMagmaSigTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutiveAddMagmaSigTerm n) → (OpInvolutiveAddMagmaSigTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutiveAddMagmaSigTerm2 n A) → (OpInvolutiveAddMagmaSigTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveAddMagmaSig A) → (InvolutiveAddMagmaSigTerm → A)) 
  | In (plusL x1 x2) := ((plus In) (evalB In x1) (evalB In x2))  
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutiveAddMagmaSig A) → ((ClInvolutiveAddMagmaSigTerm A) → A)) 
  | In (sing x1) := x1  
  | In (plusCl x1 x2) := ((plus In) (evalCl In x1) (evalCl In x2))  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutiveAddMagmaSig A) → ((vector A n) → ((OpInvolutiveAddMagmaSigTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (plusOL x1 x2) := ((plus In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutiveAddMagmaSig A) → ((vector A n) → ((OpInvolutiveAddMagmaSigTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (plusOL2 x1 x2) := ((plus In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   (P : (InvolutiveAddMagmaSigTerm → Type))  : ((∀ (x1 x2 : InvolutiveAddMagmaSigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 : InvolutiveAddMagmaSigTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutiveAddMagmaSigTerm) , (P x)))) 
  | pplusl ppriml (plusL x1 x2) := (pplusl _ _ (inductionB pplusl ppriml x1) (inductionB pplusl ppriml x2))  
  | pplusl ppriml (primL x1) := (ppriml _ (inductionB pplusl ppriml x1))  
  def inductionCl   (A : Type) (P : ((ClInvolutiveAddMagmaSigTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClInvolutiveAddMagmaSigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 : (ClInvolutiveAddMagmaSigTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutiveAddMagmaSigTerm A)) , (P x))))) 
  | psing ppluscl pprimcl (sing x1) := (psing x1)  
  | psing ppluscl pprimcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl pprimcl x1) (inductionCl psing ppluscl pprimcl x2))  
  | psing ppluscl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing ppluscl pprimcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutiveAddMagmaSigTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpInvolutiveAddMagmaSigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 : (OpInvolutiveAddMagmaSigTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutiveAddMagmaSigTerm n)) , (P x))))) 
  | pv pplusol pprimol (v x1) := (pv x1)  
  | pv pplusol pprimol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol pprimol x1) (inductionOpB pv pplusol pprimol x2))  
  | pv pplusol pprimol (primOL x1) := (pprimol _ (inductionOpB pv pplusol pprimol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutiveAddMagmaSigTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpInvolutiveAddMagmaSigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 : (OpInvolutiveAddMagmaSigTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutiveAddMagmaSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 pprimol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 pprimol2 x1) (inductionOp pv2 psing2 pplusol2 pprimol2 x2))  
  | pv2 psing2 pplusol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pplusol2 pprimol2 x1))  
  def stageB  : (InvolutiveAddMagmaSigTerm → (Staged InvolutiveAddMagmaSigTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClInvolutiveAddMagmaSigTerm A) → (Staged (ClInvolutiveAddMagmaSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpInvolutiveAddMagmaSigTerm n) → (Staged (OpInvolutiveAddMagmaSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutiveAddMagmaSigTerm2 n A) → (Staged (OpInvolutiveAddMagmaSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (primT : ((Repr A) → (Repr A))) 
  
end InvolutiveAddMagmaSig