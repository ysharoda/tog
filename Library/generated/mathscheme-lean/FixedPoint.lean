import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section FixedPoint   
  structure FixedPoint  (A : Type) : Type := 
       (prim : (A → A))
       (e : A)
       (fixes_prim_e : (prim e) = e) 
  
  open FixedPoint
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (eP : (Prod A A))
       (fixes_prim_eP : (primP eP) = eP) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Fi1 : (FixedPoint A1)) (Fi2 : (FixedPoint A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Fi1) x1)) = ((prim Fi2) (hom x1))))
       (pres_e : (hom (e Fi1)) = (e Fi2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Fi1 : (FixedPoint A1)) (Fi2 : (FixedPoint A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Fi1) x1) ((prim Fi2) y1)))))
       (interp_e : (interp (e Fi1) (e Fi2))) 
  
  inductive FixedPointTerm   : Type  
     | primL : (FixedPointTerm → FixedPointTerm) 
     | eL : FixedPointTerm  
      open FixedPointTerm 
  
  inductive ClFixedPointTerm  (A : Type) : Type  
     | sing : (A → ClFixedPointTerm) 
     | primCl : (ClFixedPointTerm → ClFixedPointTerm) 
     | eCl : ClFixedPointTerm  
      open ClFixedPointTerm 
  
  inductive OpFixedPointTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpFixedPointTerm) 
     | primOL : (OpFixedPointTerm → OpFixedPointTerm) 
     | eOL : OpFixedPointTerm  
      open OpFixedPointTerm 
  
  inductive OpFixedPointTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpFixedPointTerm2) 
     | sing2 : (A → OpFixedPointTerm2) 
     | primOL2 : (OpFixedPointTerm2 → OpFixedPointTerm2) 
     | eOL2 : OpFixedPointTerm2  
      open OpFixedPointTerm2 
  
  def simplifyCl   {A : Type}  : ((ClFixedPointTerm A) → (ClFixedPointTerm A)) 
  | (primCl eCl) := eCl  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpFixedPointTerm n) → (OpFixedPointTerm n)) 
  | (primOL eOL) := eOL  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpFixedPointTerm2 n A) → (OpFixedPointTerm2 n A)) 
  | (primOL2 eOL2) := eOL2  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((FixedPoint A) → (FixedPointTerm → A)) 
  | Fi (primL x1) := ((prim Fi) (evalB Fi x1))  
  | Fi eL := (e Fi)  
  def evalCl   {A : Type}  : ((FixedPoint A) → ((ClFixedPointTerm A) → A)) 
  | Fi (sing x1) := x1  
  | Fi (primCl x1) := ((prim Fi) (evalCl Fi x1))  
  | Fi eCl := (e Fi)  
  def evalOpB   {A : Type} {n : ℕ}  : ((FixedPoint A) → ((vector A n) → ((OpFixedPointTerm n) → A))) 
  | Fi vars (v x1) := (nth vars x1)  
  | Fi vars (primOL x1) := ((prim Fi) (evalOpB Fi vars x1))  
  | Fi vars eOL := (e Fi)  
  def evalOp   {A : Type} {n : ℕ}  : ((FixedPoint A) → ((vector A n) → ((OpFixedPointTerm2 n A) → A))) 
  | Fi vars (v2 x1) := (nth vars x1)  
  | Fi vars (sing2 x1) := x1  
  | Fi vars (primOL2 x1) := ((prim Fi) (evalOp Fi vars x1))  
  | Fi vars eOL2 := (e Fi)  
  def inductionB   {P : (FixedPointTerm → Type)}  : ((∀ (x1 : FixedPointTerm) , ((P x1) → (P (primL x1)))) → ((P eL) → (∀ (x : FixedPointTerm) , (P x)))) 
  | ppriml pel (primL x1) := (ppriml _ (inductionB ppriml pel x1))  
  | ppriml pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClFixedPointTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClFixedPointTerm A)) , ((P x1) → (P (primCl x1)))) → ((P eCl) → (∀ (x : (ClFixedPointTerm A)) , (P x))))) 
  | psing pprimcl pecl (sing x1) := (psing x1)  
  | psing pprimcl pecl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl pecl x1))  
  | psing pprimcl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpFixedPointTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpFixedPointTerm n)) , ((P x1) → (P (primOL x1)))) → ((P eOL) → (∀ (x : (OpFixedPointTerm n)) , (P x))))) 
  | pv pprimol peol (v x1) := (pv x1)  
  | pv pprimol peol (primOL x1) := (pprimol _ (inductionOpB pv pprimol peol x1))  
  | pv pprimol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpFixedPointTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpFixedPointTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P eOL2) → (∀ (x : (OpFixedPointTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 peol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 peol2 x1))  
  | pv2 psing2 pprimol2 peol2 eOL2 := peol2  
  def stageB  : (FixedPointTerm → (Staged FixedPointTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClFixedPointTerm A) → (Staged (ClFixedPointTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpFixedPointTerm n) → (Staged (OpFixedPointTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpFixedPointTerm2 n A) → (Staged (OpFixedPointTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (eT : (Repr A)) 
  
end FixedPoint