import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section UnipotentPointedMagma   
  structure UnipotentPointedMagma  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (unipotence : (∀ {x : A} , (op x x) = e)) 
  
  open UnipotentPointedMagma
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (unipotenceP : (∀ {xP : (Prod A A)} , (opP xP xP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Un1 : (UnipotentPointedMagma A1)) (Un2 : (UnipotentPointedMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Un1)) = (e Un2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Un1) x1 x2)) = ((op Un2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Un1 : (UnipotentPointedMagma A1)) (Un2 : (UnipotentPointedMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Un1) (e Un2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Un1) x1 x2) ((op Un2) y1 y2)))))) 
  
  inductive UnipotentPointedMagmaTerm   : Type  
     | eL : UnipotentPointedMagmaTerm 
     | opL : (UnipotentPointedMagmaTerm → (UnipotentPointedMagmaTerm → UnipotentPointedMagmaTerm))  
      open UnipotentPointedMagmaTerm 
  
  inductive ClUnipotentPointedMagmaTerm  (A : Type) : Type  
     | sing : (A → ClUnipotentPointedMagmaTerm) 
     | eCl : ClUnipotentPointedMagmaTerm 
     | opCl : (ClUnipotentPointedMagmaTerm → (ClUnipotentPointedMagmaTerm → ClUnipotentPointedMagmaTerm))  
      open ClUnipotentPointedMagmaTerm 
  
  inductive OpUnipotentPointedMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpUnipotentPointedMagmaTerm) 
     | eOL : OpUnipotentPointedMagmaTerm 
     | opOL : (OpUnipotentPointedMagmaTerm → (OpUnipotentPointedMagmaTerm → OpUnipotentPointedMagmaTerm))  
      open OpUnipotentPointedMagmaTerm 
  
  inductive OpUnipotentPointedMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpUnipotentPointedMagmaTerm2) 
     | sing2 : (A → OpUnipotentPointedMagmaTerm2) 
     | eOL2 : OpUnipotentPointedMagmaTerm2 
     | opOL2 : (OpUnipotentPointedMagmaTerm2 → (OpUnipotentPointedMagmaTerm2 → OpUnipotentPointedMagmaTerm2))  
      open OpUnipotentPointedMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClUnipotentPointedMagmaTerm A) → (ClUnipotentPointedMagmaTerm A)) 
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpUnipotentPointedMagmaTerm n) → (OpUnipotentPointedMagmaTerm n)) 
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpUnipotentPointedMagmaTerm2 n A) → (OpUnipotentPointedMagmaTerm2 n A)) 
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((UnipotentPointedMagma A) → (UnipotentPointedMagmaTerm → A)) 
  | Un eL := (e Un)  
  | Un (opL x1 x2) := ((op Un) (evalB Un x1) (evalB Un x2))  
  def evalCl   {A : Type}  : ((UnipotentPointedMagma A) → ((ClUnipotentPointedMagmaTerm A) → A)) 
  | Un (sing x1) := x1  
  | Un eCl := (e Un)  
  | Un (opCl x1 x2) := ((op Un) (evalCl Un x1) (evalCl Un x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((UnipotentPointedMagma A) → ((vector A n) → ((OpUnipotentPointedMagmaTerm n) → A))) 
  | Un vars (v x1) := (nth vars x1)  
  | Un vars eOL := (e Un)  
  | Un vars (opOL x1 x2) := ((op Un) (evalOpB Un vars x1) (evalOpB Un vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((UnipotentPointedMagma A) → ((vector A n) → ((OpUnipotentPointedMagmaTerm2 n A) → A))) 
  | Un vars (v2 x1) := (nth vars x1)  
  | Un vars (sing2 x1) := x1  
  | Un vars eOL2 := (e Un)  
  | Un vars (opOL2 x1 x2) := ((op Un) (evalOp Un vars x1) (evalOp Un vars x2))  
  def inductionB   (P : (UnipotentPointedMagmaTerm → Type))  : ((P eL) → ((∀ (x1 x2 : UnipotentPointedMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : UnipotentPointedMagmaTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   (A : Type) (P : ((ClUnipotentPointedMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClUnipotentPointedMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClUnipotentPointedMagmaTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpUnipotentPointedMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpUnipotentPointedMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpUnipotentPointedMagmaTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpUnipotentPointedMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpUnipotentPointedMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpUnipotentPointedMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (UnipotentPointedMagmaTerm → (Staged UnipotentPointedMagmaTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClUnipotentPointedMagmaTerm A) → (Staged (ClUnipotentPointedMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpUnipotentPointedMagmaTerm n) → (Staged (OpUnipotentPointedMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpUnipotentPointedMagmaTerm2 n A) → (Staged (OpUnipotentPointedMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end UnipotentPointedMagma