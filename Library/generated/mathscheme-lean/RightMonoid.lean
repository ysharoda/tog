import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section RightMonoid   
  structure RightMonoid  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (runit_e : (∀ {x : A} , (op x e) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z)))) 
  
  open RightMonoid
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (RightMonoid A1)) (Ri2 : (RightMonoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ri1) x1 x2)) = ((op Ri2) (hom x1) (hom x2))))
       (pres_e : (hom (e Ri1)) = (e Ri2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (RightMonoid A1)) (Ri2 : (RightMonoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2))))))
       (interp_e : (interp (e Ri1) (e Ri2))) 
  
  inductive RightMonoidTerm   : Type  
     | opL : (RightMonoidTerm → (RightMonoidTerm → RightMonoidTerm)) 
     | eL : RightMonoidTerm  
      open RightMonoidTerm 
  
  inductive ClRightMonoidTerm  (A : Type) : Type  
     | sing : (A → ClRightMonoidTerm) 
     | opCl : (ClRightMonoidTerm → (ClRightMonoidTerm → ClRightMonoidTerm)) 
     | eCl : ClRightMonoidTerm  
      open ClRightMonoidTerm 
  
  inductive OpRightMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRightMonoidTerm) 
     | opOL : (OpRightMonoidTerm → (OpRightMonoidTerm → OpRightMonoidTerm)) 
     | eOL : OpRightMonoidTerm  
      open OpRightMonoidTerm 
  
  inductive OpRightMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRightMonoidTerm2) 
     | sing2 : (A → OpRightMonoidTerm2) 
     | opOL2 : (OpRightMonoidTerm2 → (OpRightMonoidTerm2 → OpRightMonoidTerm2)) 
     | eOL2 : OpRightMonoidTerm2  
      open OpRightMonoidTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRightMonoidTerm A) → (ClRightMonoidTerm A)) 
  | (opCl x eCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRightMonoidTerm n) → (OpRightMonoidTerm n)) 
  | (opOL x eOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRightMonoidTerm2 n A) → (OpRightMonoidTerm2 n A)) 
  | (opOL2 x eOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((RightMonoid A) → (RightMonoidTerm → A)) 
  | Ri (opL x1 x2) := ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri eL := (e Ri)  
  def evalCl   {A : Type}  : ((RightMonoid A) → ((ClRightMonoidTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (opCl x1 x2) := ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri eCl := (e Ri)  
  def evalOpB   {A : Type} (n : ℕ)  : ((RightMonoid A) → ((vector A n) → ((OpRightMonoidTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (opOL x1 x2) := ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars eOL := (e Ri)  
  def evalOp   {A : Type} (n : ℕ)  : ((RightMonoid A) → ((vector A n) → ((OpRightMonoidTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (opOL2 x1 x2) := ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars eOL2 := (e Ri)  
  def inductionB   (P : (RightMonoidTerm → Type))  : ((∀ (x1 x2 : RightMonoidTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : RightMonoidTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   (A : Type) (P : ((ClRightMonoidTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRightMonoidTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClRightMonoidTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   (n : ℕ) (P : ((OpRightMonoidTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRightMonoidTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpRightMonoidTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRightMonoidTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRightMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpRightMonoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (RightMonoidTerm → (Staged RightMonoidTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   (A : Type)  : ((ClRightMonoidTerm A) → (Staged (ClRightMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   (n : ℕ)  : ((OpRightMonoidTerm n) → (Staged (OpRightMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRightMonoidTerm2 n A) → (Staged (OpRightMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end RightMonoid