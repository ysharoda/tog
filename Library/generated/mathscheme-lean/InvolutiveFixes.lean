import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveFixes   
  structure InvolutiveFixes  (A : Type) : Type := 
       (one : A)
       (prim : (A → A))
       (fixes_prim_one : (prim one) = one) 
  
  open InvolutiveFixes
  structure Sig  (AS : Type) : Type := 
       (oneS : AS)
       (primS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A))
       (primP : ((Prod A A) → (Prod A A)))
       (fixes_prim_1P : (primP oneP) = oneP) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveFixes A1)) (In2 : (InvolutiveFixes A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one In1)) = (one In2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveFixes A1)) (In2 : (InvolutiveFixes A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one In1) (one In2)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))) 
  
  inductive InvolutiveFixesTerm   : Type  
     | oneL : InvolutiveFixesTerm 
     | primL : (InvolutiveFixesTerm → InvolutiveFixesTerm)  
      open InvolutiveFixesTerm 
  
  inductive ClInvolutiveFixesTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveFixesTerm) 
     | oneCl : ClInvolutiveFixesTerm 
     | primCl : (ClInvolutiveFixesTerm → ClInvolutiveFixesTerm)  
      open ClInvolutiveFixesTerm 
  
  inductive OpInvolutiveFixesTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveFixesTerm) 
     | oneOL : OpInvolutiveFixesTerm 
     | primOL : (OpInvolutiveFixesTerm → OpInvolutiveFixesTerm)  
      open OpInvolutiveFixesTerm 
  
  inductive OpInvolutiveFixesTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveFixesTerm2) 
     | sing2 : (A → OpInvolutiveFixesTerm2) 
     | oneOL2 : OpInvolutiveFixesTerm2 
     | primOL2 : (OpInvolutiveFixesTerm2 → OpInvolutiveFixesTerm2)  
      open OpInvolutiveFixesTerm2 
  
  def simplifyCl   {A : Type}  : ((ClInvolutiveFixesTerm A) → (ClInvolutiveFixesTerm A)) 
  | (primCl oneCl) := oneCl  
  | oneCl := oneCl  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpInvolutiveFixesTerm n) → (OpInvolutiveFixesTerm n)) 
  | (primOL oneOL) := oneOL  
  | oneOL := oneOL  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpInvolutiveFixesTerm2 n A) → (OpInvolutiveFixesTerm2 n A)) 
  | (primOL2 oneOL2) := oneOL2  
  | oneOL2 := oneOL2  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveFixes A) → (InvolutiveFixesTerm → A)) 
  | In oneL := (one In)  
  | In (primL x1) := ((prim In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutiveFixes A) → ((ClInvolutiveFixesTerm A) → A)) 
  | In (sing x1) := x1  
  | In oneCl := (one In)  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((InvolutiveFixes A) → ((vector A n) → ((OpInvolutiveFixesTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars oneOL := (one In)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((InvolutiveFixes A) → ((vector A n) → ((OpInvolutiveFixesTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars oneOL2 := (one In)  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  def inductionB   {P : (InvolutiveFixesTerm → Type)}  : ((P oneL) → ((∀ (x1 : InvolutiveFixesTerm) , ((P x1) → (P (primL x1)))) → (∀ (x : InvolutiveFixesTerm) , (P x)))) 
  | p1l ppriml oneL := p1l  
  | p1l ppriml (primL x1) := (ppriml _ (inductionB p1l ppriml x1))  
  def inductionCl   {A : Type} {P : ((ClInvolutiveFixesTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → ((∀ (x1 : (ClInvolutiveFixesTerm A)) , ((P x1) → (P (primCl x1)))) → (∀ (x : (ClInvolutiveFixesTerm A)) , (P x))))) 
  | psing p1cl pprimcl (sing x1) := (psing x1)  
  | psing p1cl pprimcl oneCl := p1cl  
  | psing p1cl pprimcl (primCl x1) := (pprimcl _ (inductionCl psing p1cl pprimcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpInvolutiveFixesTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → ((∀ (x1 : (OpInvolutiveFixesTerm n)) , ((P x1) → (P (primOL x1)))) → (∀ (x : (OpInvolutiveFixesTerm n)) , (P x))))) 
  | pv p1ol pprimol (v x1) := (pv x1)  
  | pv p1ol pprimol oneOL := p1ol  
  | pv p1ol pprimol (primOL x1) := (pprimol _ (inductionOpB pv p1ol pprimol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpInvolutiveFixesTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → ((∀ (x1 : (OpInvolutiveFixesTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → (∀ (x : (OpInvolutiveFixesTerm2 n A)) , (P x)))))) 
  | pv2 psing2 p1ol2 pprimol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 pprimol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 pprimol2 oneOL2 := p1ol2  
  | pv2 psing2 p1ol2 pprimol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 p1ol2 pprimol2 x1))  
  def stageB  : (InvolutiveFixesTerm → (Staged InvolutiveFixesTerm))
  | oneL := (Now oneL)  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClInvolutiveFixesTerm A) → (Staged (ClInvolutiveFixesTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpInvolutiveFixesTerm n) → (Staged (OpInvolutiveFixesTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpInvolutiveFixesTerm2 n A) → (Staged (OpInvolutiveFixesTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A))
       (primT : ((Repr A) → (Repr A))) 
  
end InvolutiveFixes