import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedSteinerMagma   
  structure PointedSteinerMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x)))
       (antiAbsorbent : (∀ {x y : A} , (op x (op x y)) = y)) 
  
  open PointedSteinerMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP)))
       (antiAbsorbentP : (∀ {xP yP : (Prod A A)} , (opP xP (opP xP yP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedSteinerMagma A1)) (Po2 : (PointedSteinerMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Po1) x1 x2)) = ((op Po2) (hom x1) (hom x2))))
       (pres_e : (hom (e Po1)) = (e Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedSteinerMagma A1)) (Po2 : (PointedSteinerMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Po1) x1 x2) ((op Po2) y1 y2))))))
       (interp_e : (interp (e Po1) (e Po2))) 
  
  inductive PointedSteinerMagmaTerm   : Type  
     | opL : (PointedSteinerMagmaTerm → (PointedSteinerMagmaTerm → PointedSteinerMagmaTerm)) 
     | eL : PointedSteinerMagmaTerm  
      open PointedSteinerMagmaTerm 
  
  inductive ClPointedSteinerMagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointedSteinerMagmaTerm) 
     | opCl : (ClPointedSteinerMagmaTerm → (ClPointedSteinerMagmaTerm → ClPointedSteinerMagmaTerm)) 
     | eCl : ClPointedSteinerMagmaTerm  
      open ClPointedSteinerMagmaTerm 
  
  inductive OpPointedSteinerMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedSteinerMagmaTerm) 
     | opOL : (OpPointedSteinerMagmaTerm → (OpPointedSteinerMagmaTerm → OpPointedSteinerMagmaTerm)) 
     | eOL : OpPointedSteinerMagmaTerm  
      open OpPointedSteinerMagmaTerm 
  
  inductive OpPointedSteinerMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedSteinerMagmaTerm2) 
     | sing2 : (A → OpPointedSteinerMagmaTerm2) 
     | opOL2 : (OpPointedSteinerMagmaTerm2 → (OpPointedSteinerMagmaTerm2 → OpPointedSteinerMagmaTerm2)) 
     | eOL2 : OpPointedSteinerMagmaTerm2  
      open OpPointedSteinerMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClPointedSteinerMagmaTerm A) → (ClPointedSteinerMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpPointedSteinerMagmaTerm n) → (OpPointedSteinerMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpPointedSteinerMagmaTerm2 n A) → (OpPointedSteinerMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedSteinerMagma A) → (PointedSteinerMagmaTerm → A)) 
  | Po (opL x1 x2) := ((op Po) (evalB Po x1) (evalB Po x2))  
  | Po eL := (e Po)  
  def evalCl   {A : Type}  : ((PointedSteinerMagma A) → ((ClPointedSteinerMagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po (opCl x1 x2) := ((op Po) (evalCl Po x1) (evalCl Po x2))  
  | Po eCl := (e Po)  
  def evalOpB   {A : Type} (n : ℕ)  : ((PointedSteinerMagma A) → ((vector A n) → ((OpPointedSteinerMagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars (opOL x1 x2) := ((op Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  | Po vars eOL := (e Po)  
  def evalOp   {A : Type} (n : ℕ)  : ((PointedSteinerMagma A) → ((vector A n) → ((OpPointedSteinerMagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars (opOL2 x1 x2) := ((op Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  | Po vars eOL2 := (e Po)  
  def inductionB   (P : (PointedSteinerMagmaTerm → Type))  : ((∀ (x1 x2 : PointedSteinerMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : PointedSteinerMagmaTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   (A : Type) (P : ((ClPointedSteinerMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPointedSteinerMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClPointedSteinerMagmaTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   (n : ℕ) (P : ((OpPointedSteinerMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPointedSteinerMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpPointedSteinerMagmaTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpPointedSteinerMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPointedSteinerMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpPointedSteinerMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (PointedSteinerMagmaTerm → (Staged PointedSteinerMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   (A : Type)  : ((ClPointedSteinerMagmaTerm A) → (Staged (ClPointedSteinerMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   (n : ℕ)  : ((OpPointedSteinerMagmaTerm n) → (Staged (OpPointedSteinerMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpPointedSteinerMagmaTerm2 n A) → (Staged (OpPointedSteinerMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end PointedSteinerMagma