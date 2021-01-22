import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedMagma   
  structure PointedMagma  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A))) 
  
  open PointedMagma
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedMagma A1)) (Po2 : (PointedMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Po1)) = (e Po2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Po1) x1 x2)) = ((op Po2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedMagma A1)) (Po2 : (PointedMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Po1) (e Po2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2)))))) 
  
  inductive PointedMagmaTerm   : Type  
     | eL : PointedMagmaTerm 
     | opL : (PointedMagmaTerm → (PointedMagmaTerm → PointedMagmaTerm))  
      open PointedMagmaTerm 
  
  inductive ClPointedMagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointedMagmaTerm) 
     | eCl : ClPointedMagmaTerm 
     | opCl : (ClPointedMagmaTerm → (ClPointedMagmaTerm → ClPointedMagmaTerm))  
      open ClPointedMagmaTerm 
  
  inductive OpPointedMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedMagmaTerm) 
     | eOL : OpPointedMagmaTerm 
     | opOL : (OpPointedMagmaTerm → (OpPointedMagmaTerm → OpPointedMagmaTerm))  
      open OpPointedMagmaTerm 
  
  inductive OpPointedMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedMagmaTerm2) 
     | sing2 : (A → OpPointedMagmaTerm2) 
     | eOL2 : OpPointedMagmaTerm2 
     | opOL2 : (OpPointedMagmaTerm2 → (OpPointedMagmaTerm2 → OpPointedMagmaTerm2))  
      open OpPointedMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPointedMagmaTerm A) → (ClPointedMagmaTerm A)) 
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPointedMagmaTerm n) → (OpPointedMagmaTerm n)) 
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPointedMagmaTerm2 n A) → (OpPointedMagmaTerm2 n A)) 
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedMagma A) → (PointedMagmaTerm → A)) 
  | Po eL := (e Po)  
  | Po (opL x1 x2) := ((op Po) (evalB Po x1) (evalB Po x2))  
  def evalCl   {A : Type}  : ((PointedMagma A) → ((ClPointedMagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po eCl := (e Po)  
  | Po (opCl x1 x2) := ((op Po) (evalCl Po x1) (evalCl Po x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((PointedMagma A) → ((vector A n) → ((OpPointedMagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars eOL := (e Po)  
  | Po vars (opOL x1 x2) := ((op Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((PointedMagma A) → ((vector A n) → ((OpPointedMagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars eOL2 := (e Po)  
  | Po vars (opOL2 x1 x2) := ((op Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  def inductionB   {P : (PointedMagmaTerm → Type)}  : ((P eL) → ((∀ (x1 x2 : PointedMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : PointedMagmaTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   {A : Type} {P : ((ClPointedMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClPointedMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClPointedMagmaTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpPointedMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpPointedMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpPointedMagmaTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPointedMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpPointedMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpPointedMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (PointedMagmaTerm → (Staged PointedMagmaTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClPointedMagmaTerm A) → (Staged (ClPointedMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpPointedMagmaTerm n) → (Staged (OpPointedMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPointedMagmaTerm2 n A) → (Staged (OpPointedMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end PointedMagma