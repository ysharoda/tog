import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InverseSig   
  structure InverseSig  (A : Type) : Type := 
       (inv : (A → A))
       (e : A)
       (op : (A → (A → A))) 
  
  open InverseSig
  structure Sig  (AS : Type) : Type := 
       (invS : (AS → AS))
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (invP : ((Prod A A) → (Prod A A)))
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InverseSig A1)) (In2 : (InverseSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv In1) x1)) = ((inv In2) (hom x1))))
       (pres_e : (hom (e In1)) = (e In2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op In1) x1 x2)) = ((op In2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InverseSig A1)) (In2 : (InverseSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv In1) x1) ((inv In2) y1)))))
       (interp_e : (interp (e In1) (e In2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op In1) x1 x2) ((op In2) y1 y2)))))) 
  
  inductive InverseSigTerm   : Type  
     | invL : (InverseSigTerm → InverseSigTerm) 
     | eL : InverseSigTerm 
     | opL : (InverseSigTerm → (InverseSigTerm → InverseSigTerm))  
      open InverseSigTerm 
  
  inductive ClInverseSigTerm  (A : Type) : Type  
     | sing : (A → ClInverseSigTerm) 
     | invCl : (ClInverseSigTerm → ClInverseSigTerm) 
     | eCl : ClInverseSigTerm 
     | opCl : (ClInverseSigTerm → (ClInverseSigTerm → ClInverseSigTerm))  
      open ClInverseSigTerm 
  
  inductive OpInverseSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInverseSigTerm) 
     | invOL : (OpInverseSigTerm → OpInverseSigTerm) 
     | eOL : OpInverseSigTerm 
     | opOL : (OpInverseSigTerm → (OpInverseSigTerm → OpInverseSigTerm))  
      open OpInverseSigTerm 
  
  inductive OpInverseSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInverseSigTerm2) 
     | sing2 : (A → OpInverseSigTerm2) 
     | invOL2 : (OpInverseSigTerm2 → OpInverseSigTerm2) 
     | eOL2 : OpInverseSigTerm2 
     | opOL2 : (OpInverseSigTerm2 → (OpInverseSigTerm2 → OpInverseSigTerm2))  
      open OpInverseSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInverseSigTerm A) → (ClInverseSigTerm A)) 
  | (invCl x1) := (invCl (simplifyCl x1))  
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInverseSigTerm n) → (OpInverseSigTerm n)) 
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInverseSigTerm2 n A) → (OpInverseSigTerm2 n A)) 
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InverseSig A) → (InverseSigTerm → A)) 
  | In (invL x1) := ((inv In) (evalB In x1))  
  | In eL := (e In)  
  | In (opL x1 x2) := ((op In) (evalB In x1) (evalB In x2))  
  def evalCl   {A : Type}  : ((InverseSig A) → ((ClInverseSigTerm A) → A)) 
  | In (sing x1) := x1  
  | In (invCl x1) := ((inv In) (evalCl In x1))  
  | In eCl := (e In)  
  | In (opCl x1 x2) := ((op In) (evalCl In x1) (evalCl In x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InverseSig A) → ((vector A n) → ((OpInverseSigTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (invOL x1) := ((inv In) (evalOpB In vars x1))  
  | In vars eOL := (e In)  
  | In vars (opOL x1 x2) := ((op In) (evalOpB In vars x1) (evalOpB In vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((InverseSig A) → ((vector A n) → ((OpInverseSigTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (invOL2 x1) := ((inv In) (evalOp In vars x1))  
  | In vars eOL2 := (e In)  
  | In vars (opOL2 x1 x2) := ((op In) (evalOp In vars x1) (evalOp In vars x2))  
  def inductionB   {P : (InverseSigTerm → Type)}  : ((∀ (x1 : InverseSigTerm) , ((P x1) → (P (invL x1)))) → ((P eL) → ((∀ (x1 x2 : InverseSigTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : InverseSigTerm) , (P x))))) 
  | pinvl pel popl (invL x1) := (pinvl _ (inductionB pinvl pel popl x1))  
  | pinvl pel popl eL := pel  
  | pinvl pel popl (opL x1 x2) := (popl _ _ (inductionB pinvl pel popl x1) (inductionB pinvl pel popl x2))  
  def inductionCl   {A : Type} {P : ((ClInverseSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInverseSigTerm A)) , ((P x1) → (P (invCl x1)))) → ((P eCl) → ((∀ (x1 x2 : (ClInverseSigTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClInverseSigTerm A)) , (P x)))))) 
  | psing pinvcl pecl popcl (sing x1) := (psing x1)  
  | psing pinvcl pecl popcl (invCl x1) := (pinvcl _ (inductionCl psing pinvcl pecl popcl x1))  
  | psing pinvcl pecl popcl eCl := pecl  
  | psing pinvcl pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pinvcl pecl popcl x1) (inductionCl psing pinvcl pecl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpInverseSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInverseSigTerm n)) , ((P x1) → (P (invOL x1)))) → ((P eOL) → ((∀ (x1 x2 : (OpInverseSigTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpInverseSigTerm n)) , (P x)))))) 
  | pv pinvol peol popol (v x1) := (pv x1)  
  | pv pinvol peol popol (invOL x1) := (pinvol _ (inductionOpB pv pinvol peol popol x1))  
  | pv pinvol peol popol eOL := peol  
  | pv pinvol peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pinvol peol popol x1) (inductionOpB pv pinvol peol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInverseSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInverseSigTerm2 n A)) , ((P x1) → (P (invOL2 x1)))) → ((P eOL2) → ((∀ (x1 x2 : (OpInverseSigTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpInverseSigTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pinvol2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pinvol2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 pinvol2 peol2 popol2 x1))  
  | pv2 psing2 pinvol2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pinvol2 peol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 peol2 popol2 x2))  
  def stageB  : (InverseSigTerm → (Staged InverseSigTerm))
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClInverseSigTerm A) → (Staged (ClInverseSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpInverseSigTerm n) → (Staged (OpInverseSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInverseSigTerm2 n A) → (Staged (OpInverseSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (invT : ((Repr A) → (Repr A)))
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end InverseSig