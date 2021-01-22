import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedSemigroup   
  structure PointedSemigroup  (A : Type) : Type := 
       (op : (A → (A → A)))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (e : A) 
  
  open PointedSemigroup
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedSemigroup A1)) (Po2 : (PointedSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Po1) x1 x2)) = ((op Po2) (hom x1) (hom x2))))
       (pres_e : (hom (e Po1)) = (e Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedSemigroup A1)) (Po2 : (PointedSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2))))))
       (interp_e : (interp (e Po1) (e Po2))) 
  
  inductive PointedSemigroupTerm   : Type  
     | opL : (PointedSemigroupTerm → (PointedSemigroupTerm → PointedSemigroupTerm)) 
     | eL : PointedSemigroupTerm  
      open PointedSemigroupTerm 
  
  inductive ClPointedSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClPointedSemigroupTerm) 
     | opCl : (ClPointedSemigroupTerm → (ClPointedSemigroupTerm → ClPointedSemigroupTerm)) 
     | eCl : ClPointedSemigroupTerm  
      open ClPointedSemigroupTerm 
  
  inductive OpPointedSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedSemigroupTerm) 
     | opOL : (OpPointedSemigroupTerm → (OpPointedSemigroupTerm → OpPointedSemigroupTerm)) 
     | eOL : OpPointedSemigroupTerm  
      open OpPointedSemigroupTerm 
  
  inductive OpPointedSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedSemigroupTerm2) 
     | sing2 : (A → OpPointedSemigroupTerm2) 
     | opOL2 : (OpPointedSemigroupTerm2 → (OpPointedSemigroupTerm2 → OpPointedSemigroupTerm2)) 
     | eOL2 : OpPointedSemigroupTerm2  
      open OpPointedSemigroupTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPointedSemigroupTerm A) → (ClPointedSemigroupTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPointedSemigroupTerm n) → (OpPointedSemigroupTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPointedSemigroupTerm2 n A) → (OpPointedSemigroupTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedSemigroup A) → (PointedSemigroupTerm → A)) 
  | Po (opL x1 x2) := ((op Po) (evalB Po x1) (evalB Po x2))  
  | Po eL := (e Po)  
  def evalCl   {A : Type}  : ((PointedSemigroup A) → ((ClPointedSemigroupTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po (opCl x1 x2) := ((op Po) (evalCl Po x1) (evalCl Po x2))  
  | Po eCl := (e Po)  
  def evalOpB   {A : Type} {n : ℕ}  : ((PointedSemigroup A) → ((vector A n) → ((OpPointedSemigroupTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars (opOL x1 x2) := ((op Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  | Po vars eOL := (e Po)  
  def evalOp   {A : Type} {n : ℕ}  : ((PointedSemigroup A) → ((vector A n) → ((OpPointedSemigroupTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars (opOL2 x1 x2) := ((op Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  | Po vars eOL2 := (e Po)  
  def inductionB   {P : (PointedSemigroupTerm → Type)}  : ((∀ (x1 x2 : PointedSemigroupTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : PointedSemigroupTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClPointedSemigroupTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPointedSemigroupTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClPointedSemigroupTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpPointedSemigroupTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPointedSemigroupTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpPointedSemigroupTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPointedSemigroupTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPointedSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpPointedSemigroupTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (PointedSemigroupTerm → (Staged PointedSemigroupTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClPointedSemigroupTerm A) → (Staged (ClPointedSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpPointedSemigroupTerm n) → (Staged (OpPointedSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPointedSemigroupTerm2 n A) → (Staged (OpPointedSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end PointedSemigroup