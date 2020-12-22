import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedUnarySystem   
  structure PointedUnarySystem  (A : Type) : Type := 
       (prim : (A → A))
       (e : A) 
  
  open PointedUnarySystem
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (eP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedUnarySystem A1)) (Po2 : (PointedUnarySystem A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Po1) x1)) = ((prim Po2) (hom x1))))
       (pres_e : (hom (e Po1)) = (e Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedUnarySystem A1)) (Po2 : (PointedUnarySystem A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Po1) x1) ((prim Po2) y1)))))
       (interp_e : (interp (e Po1) (e Po2))) 
  
  inductive PointedUnarySystemTerm   : Type  
     | primL : (PointedUnarySystemTerm → PointedUnarySystemTerm) 
     | eL : PointedUnarySystemTerm  
      open PointedUnarySystemTerm 
  
  inductive ClPointedUnarySystemTerm  (A : Type) : Type  
     | sing : (A → ClPointedUnarySystemTerm) 
     | primCl : (ClPointedUnarySystemTerm → ClPointedUnarySystemTerm) 
     | eCl : ClPointedUnarySystemTerm  
      open ClPointedUnarySystemTerm 
  
  inductive OpPointedUnarySystemTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedUnarySystemTerm) 
     | primOL : (OpPointedUnarySystemTerm → OpPointedUnarySystemTerm) 
     | eOL : OpPointedUnarySystemTerm  
      open OpPointedUnarySystemTerm 
  
  inductive OpPointedUnarySystemTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedUnarySystemTerm2) 
     | sing2 : (A → OpPointedUnarySystemTerm2) 
     | primOL2 : (OpPointedUnarySystemTerm2 → OpPointedUnarySystemTerm2) 
     | eOL2 : OpPointedUnarySystemTerm2  
      open OpPointedUnarySystemTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointedUnarySystemTerm A) → (ClPointedUnarySystemTerm A)) 
  | (primCl x1) := (primCl (simplifyCl x1))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointedUnarySystemTerm n) → (OpPointedUnarySystemTerm n)) 
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointedUnarySystemTerm2 n A) → (OpPointedUnarySystemTerm2 n A)) 
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedUnarySystem A) → (PointedUnarySystemTerm → A)) 
  | Po (primL x1) := ((prim Po) (evalB Po x1))  
  | Po eL := (e Po)  
  def evalCl   {A : Type}  : ((PointedUnarySystem A) → ((ClPointedUnarySystemTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po (primCl x1) := ((prim Po) (evalCl Po x1))  
  | Po eCl := (e Po)  
  def evalOpB   {A : Type} (n : ℕ)  : ((PointedUnarySystem A) → ((vector A n) → ((OpPointedUnarySystemTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars (primOL x1) := ((prim Po) (evalOpB Po vars x1))  
  | Po vars eOL := (e Po)  
  def evalOp   {A : Type} (n : ℕ)  : ((PointedUnarySystem A) → ((vector A n) → ((OpPointedUnarySystemTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars (primOL2 x1) := ((prim Po) (evalOp Po vars x1))  
  | Po vars eOL2 := (e Po)  
  def inductionB   (P : (PointedUnarySystemTerm → Type))  : ((∀ (x1 : PointedUnarySystemTerm) , ((P x1) → (P (primL x1)))) → ((P eL) → (∀ (x : PointedUnarySystemTerm) , (P x)))) 
  | ppriml pel (primL x1) := (ppriml _ (inductionB ppriml pel x1))  
  | ppriml pel eL := pel  
  def inductionCl   (A : Type) (P : ((ClPointedUnarySystemTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClPointedUnarySystemTerm A)) , ((P x1) → (P (primCl x1)))) → ((P eCl) → (∀ (x : (ClPointedUnarySystemTerm A)) , (P x))))) 
  | psing pprimcl pecl (sing x1) := (psing x1)  
  | psing pprimcl pecl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl pecl x1))  
  | psing pprimcl pecl eCl := pecl  
  def inductionOpB   (n : ℕ) (P : ((OpPointedUnarySystemTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpPointedUnarySystemTerm n)) , ((P x1) → (P (primOL x1)))) → ((P eOL) → (∀ (x : (OpPointedUnarySystemTerm n)) , (P x))))) 
  | pv pprimol peol (v x1) := (pv x1)  
  | pv pprimol peol (primOL x1) := (pprimol _ (inductionOpB pv pprimol peol x1))  
  | pv pprimol peol eOL := peol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointedUnarySystemTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpPointedUnarySystemTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P eOL2) → (∀ (x : (OpPointedUnarySystemTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 peol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 peol2 x1))  
  | pv2 psing2 pprimol2 peol2 eOL2 := peol2  
  def stageB  : (PointedUnarySystemTerm → (Staged PointedUnarySystemTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | eL := (Now eL)  
  def stageCl   (A : Type)  : ((ClPointedUnarySystemTerm A) → (Staged (ClPointedUnarySystemTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | eCl := (Now eCl)  
  def stageOpB   (n : ℕ)  : ((OpPointedUnarySystemTerm n) → (Staged (OpPointedUnarySystemTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | eOL := (Now eOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointedUnarySystemTerm2 n A) → (Staged (OpPointedUnarySystemTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (eT : (Repr A)) 
  
end PointedUnarySystem