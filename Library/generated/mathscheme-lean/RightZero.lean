import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightZero   
  structure RightZero  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (rightZero_op_e : (∀ {x : A} , (op x e) = e)) 
  
  open RightZero
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightZero_op_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightZero A1)) (Ri2 : (RightZero A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Ri1)) = (e Ri2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ri1) x1 x2)) = ((op Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightZero A1)) (Ri2 : (RightZero A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Ri1) (e Ri2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))) 
  
  inductive RightZeroTerm   : Type  
     | eL : RightZeroTerm 
     | opL : (RightZeroTerm → (RightZeroTerm → RightZeroTerm))  
      open RightZeroTerm 
  
  inductive ClRightZeroTerm  (A : Type) : Type  
     | sing : (A → ClRightZeroTerm) 
     | eCl : ClRightZeroTerm 
     | opCl : (ClRightZeroTerm → (ClRightZeroTerm → ClRightZeroTerm))  
      open ClRightZeroTerm 
  
  inductive OpRightZeroTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightZeroTerm) 
     | eOL : OpRightZeroTerm 
     | opOL : (OpRightZeroTerm → (OpRightZeroTerm → OpRightZeroTerm))  
      open OpRightZeroTerm 
  
  inductive OpRightZeroTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightZeroTerm2) 
     | sing2 : (A → OpRightZeroTerm2) 
     | eOL2 : OpRightZeroTerm2 
     | opOL2 : (OpRightZeroTerm2 → (OpRightZeroTerm2 → OpRightZeroTerm2))  
      open OpRightZeroTerm2 
  
  def simplifyCl   {A : Type}  : ((ClRightZeroTerm A) → (ClRightZeroTerm A)) 
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRightZeroTerm n) → (OpRightZeroTerm n)) 
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRightZeroTerm2 n A) → (OpRightZeroTerm2 n A)) 
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightZero A) → (RightZeroTerm → A)) 
  | Ri eL := (e Ri)  
  | Ri (opL x1 x2) := ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((RightZero A) → ((ClRightZeroTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri eCl := (e Ri)  
  | Ri (opCl x1 x2) := ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((RightZero A) → ((vector A n) → ((OpRightZeroTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars eOL := (e Ri)  
  | Ri vars (opOL x1 x2) := ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((RightZero A) → ((vector A n) → ((OpRightZeroTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars eOL2 := (e Ri)  
  | Ri vars (opOL2 x1 x2) := ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (RightZeroTerm → Type)}  : ((P eL) → ((∀ (x1 x2 : RightZeroTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : RightZeroTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   {A : Type} {P : ((ClRightZeroTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClRightZeroTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClRightZeroTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRightZeroTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpRightZeroTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpRightZeroTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRightZeroTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpRightZeroTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpRightZeroTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (RightZeroTerm → (Staged RightZeroTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRightZeroTerm A) → (Staged (ClRightZeroTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRightZeroTerm n) → (Staged (OpRightZeroTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRightZeroTerm2 n A) → (Staged (OpRightZeroTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end RightZero