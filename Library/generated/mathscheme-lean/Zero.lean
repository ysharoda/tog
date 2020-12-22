import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Zero   
  structure Zero  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (leftZero_op_e : (∀ {x : A} , (op e x) = e))
       (rightZero_op_e : (∀ {x : A} , (op x e) = e)) 
  
  open Zero
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftZero_op_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = eP))
       (rightZero_op_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ze1 : (Zero A1)) (Ze2 : (Zero A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Ze1)) = (e Ze2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ze1) x1 x2)) = ((op Ze2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ze1 : (Zero A1)) (Ze2 : (Zero A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Ze1) (e Ze2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ze1) x1 x2) ((op Ze2) y1 y2)))))) 
  
  inductive ZeroTerm   : Type  
     | eL : ZeroTerm 
     | opL : (ZeroTerm → (ZeroTerm → ZeroTerm))  
      open ZeroTerm 
  
  inductive ClZeroTerm  (A : Type) : Type  
     | sing : (A → ClZeroTerm) 
     | eCl : ClZeroTerm 
     | opCl : (ClZeroTerm → (ClZeroTerm → ClZeroTerm))  
      open ClZeroTerm 
  
  inductive OpZeroTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpZeroTerm) 
     | eOL : OpZeroTerm 
     | opOL : (OpZeroTerm → (OpZeroTerm → OpZeroTerm))  
      open OpZeroTerm 
  
  inductive OpZeroTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpZeroTerm2) 
     | sing2 : (A → OpZeroTerm2) 
     | eOL2 : OpZeroTerm2 
     | opOL2 : (OpZeroTerm2 → (OpZeroTerm2 → OpZeroTerm2))  
      open OpZeroTerm2 
  
  def simplifyCl   (A : Type)  : ((ClZeroTerm A) → (ClZeroTerm A)) 
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpZeroTerm n) → (OpZeroTerm n)) 
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpZeroTerm2 n A) → (OpZeroTerm2 n A)) 
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Zero A) → (ZeroTerm → A)) 
  | Ze eL := (e Ze)  
  | Ze (opL x1 x2) := ((op Ze) (evalB Ze x1) (evalB Ze x2))  
  def evalCl   {A : Type}  : ((Zero A) → ((ClZeroTerm A) → A)) 
  | Ze (sing x1) := x1  
  | Ze eCl := (e Ze)  
  | Ze (opCl x1 x2) := ((op Ze) (evalCl Ze x1) (evalCl Ze x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Zero A) → ((vector A n) → ((OpZeroTerm n) → A))) 
  | Ze vars (v x1) := (nth vars x1)  
  | Ze vars eOL := (e Ze)  
  | Ze vars (opOL x1 x2) := ((op Ze) (evalOpB Ze vars x1) (evalOpB Ze vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Zero A) → ((vector A n) → ((OpZeroTerm2 n A) → A))) 
  | Ze vars (v2 x1) := (nth vars x1)  
  | Ze vars (sing2 x1) := x1  
  | Ze vars eOL2 := (e Ze)  
  | Ze vars (opOL2 x1 x2) := ((op Ze) (evalOp Ze vars x1) (evalOp Ze vars x2))  
  def inductionB   (P : (ZeroTerm → Type))  : ((P eL) → ((∀ (x1 x2 : ZeroTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : ZeroTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   (A : Type) (P : ((ClZeroTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClZeroTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClZeroTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpZeroTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpZeroTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpZeroTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpZeroTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpZeroTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpZeroTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (ZeroTerm → (Staged ZeroTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClZeroTerm A) → (Staged (ClZeroTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpZeroTerm n) → (Staged (OpZeroTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpZeroTerm2 n A) → (Staged (OpZeroTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Zero