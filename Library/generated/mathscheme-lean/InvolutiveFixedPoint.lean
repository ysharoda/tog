import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveFixedPoint   
  structure InvolutiveFixedPoint  (A : Type) : Type := 
       (prim : (A → A))
       (one : A)
       (fixes_prim_one : (prim one) = one)
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x)) 
  
  open InvolutiveFixedPoint
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (oneP : (Prod A A))
       (fixes_prim_1P : (primP oneP) = oneP)
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveFixedPoint A1)) (In2 : (InvolutiveFixedPoint A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_one : (hom (one In1)) = (one In2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveFixedPoint A1)) (In2 : (InvolutiveFixedPoint A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_one : (interp (one In1) (one In2))) 
  
  inductive InvolutiveFixedPointTerm   : Type  
     | primL : (InvolutiveFixedPointTerm → InvolutiveFixedPointTerm) 
     | oneL : InvolutiveFixedPointTerm  
      open InvolutiveFixedPointTerm 
  
  inductive ClInvolutiveFixedPointTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveFixedPointTerm) 
     | primCl : (ClInvolutiveFixedPointTerm → ClInvolutiveFixedPointTerm) 
     | oneCl : ClInvolutiveFixedPointTerm  
      open ClInvolutiveFixedPointTerm 
  
  inductive OpInvolutiveFixedPointTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveFixedPointTerm) 
     | primOL : (OpInvolutiveFixedPointTerm → OpInvolutiveFixedPointTerm) 
     | oneOL : OpInvolutiveFixedPointTerm  
      open OpInvolutiveFixedPointTerm 
  
  inductive OpInvolutiveFixedPointTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveFixedPointTerm2) 
     | sing2 : (A → OpInvolutiveFixedPointTerm2) 
     | primOL2 : (OpInvolutiveFixedPointTerm2 → OpInvolutiveFixedPointTerm2) 
     | oneOL2 : OpInvolutiveFixedPointTerm2  
      open OpInvolutiveFixedPointTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutiveFixedPointTerm A) → (ClInvolutiveFixedPointTerm A)) 
  | (primCl oneCl) := oneCl  
  | (primCl (primCl x)) := x  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutiveFixedPointTerm n) → (OpInvolutiveFixedPointTerm n)) 
  | (primOL oneOL) := oneOL  
  | (primOL (primOL x)) := x  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutiveFixedPointTerm2 n A) → (OpInvolutiveFixedPointTerm2 n A)) 
  | (primOL2 oneOL2) := oneOL2  
  | (primOL2 (primOL2 x)) := x  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveFixedPoint A) → (InvolutiveFixedPointTerm → A)) 
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In oneL := (one In)  
  def evalCl   {A : Type}  : ((InvolutiveFixedPoint A) → ((ClInvolutiveFixedPointTerm A) → A)) 
  | In (sing x1) := x1  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In oneCl := (one In)  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutiveFixedPoint A) → ((vector A n) → ((OpInvolutiveFixedPointTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars oneOL := (one In)  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutiveFixedPoint A) → ((vector A n) → ((OpInvolutiveFixedPointTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars oneOL2 := (one In)  
  def inductionB   (P : (InvolutiveFixedPointTerm → Type))  : ((∀ (x1 : InvolutiveFixedPointTerm) , ((P x1) → (P (primL x1)))) → ((P oneL) → (∀ (x : InvolutiveFixedPointTerm) , (P x)))) 
  | ppriml p1l (primL x1) := (ppriml _ (inductionB ppriml p1l x1))  
  | ppriml p1l oneL := p1l  
  def inductionCl   (A : Type) (P : ((ClInvolutiveFixedPointTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClInvolutiveFixedPointTerm A)) , ((P x1) → (P (primCl x1)))) → ((P oneCl) → (∀ (x : (ClInvolutiveFixedPointTerm A)) , (P x))))) 
  | psing pprimcl p1cl (sing x1) := (psing x1)  
  | psing pprimcl p1cl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl p1cl x1))  
  | psing pprimcl p1cl oneCl := p1cl  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutiveFixedPointTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpInvolutiveFixedPointTerm n)) , ((P x1) → (P (primOL x1)))) → ((P oneOL) → (∀ (x : (OpInvolutiveFixedPointTerm n)) , (P x))))) 
  | pv pprimol p1ol (v x1) := (pv x1)  
  | pv pprimol p1ol (primOL x1) := (pprimol _ (inductionOpB pv pprimol p1ol x1))  
  | pv pprimol p1ol oneOL := p1ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutiveFixedPointTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpInvolutiveFixedPointTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P oneOL2) → (∀ (x : (OpInvolutiveFixedPointTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 p1ol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 p1ol2 x1))  
  | pv2 psing2 pprimol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (InvolutiveFixedPointTerm → (Staged InvolutiveFixedPointTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | oneL := (Now oneL)  
  def stageCl   (A : Type)  : ((ClInvolutiveFixedPointTerm A) → (Staged (ClInvolutiveFixedPointTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | oneCl := (Now oneCl)  
  def stageOpB   (n : ℕ)  : ((OpInvolutiveFixedPointTerm n) → (Staged (OpInvolutiveFixedPointTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | oneOL := (Now oneOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutiveFixedPointTerm2 n A) → (Staged (OpInvolutiveFixedPointTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (oneT : (Repr A)) 
  
end InvolutiveFixedPoint