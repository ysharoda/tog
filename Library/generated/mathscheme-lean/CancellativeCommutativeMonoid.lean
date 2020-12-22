import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CancellativeCommutativeMonoid   
  structure CancellativeCommutativeMonoid  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (runit_e : (∀ {x : A} , (op x e) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z))))
       (leftCancellative : (∀ {x y z : A} , ((op z x) = (op z y) → x = y)))
       (rightCancellative : (∀ {x y z : A} , ((op x z) = (op y z) → x = y)))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x))) 
  
  open CancellativeCommutativeMonoid
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP))))
       (leftCancellativeP : (∀ {xP yP zP : (Prod A A)} , ((opP zP xP) = (opP zP yP) → xP = yP)))
       (rightCancellativeP : (∀ {xP yP zP : (Prod A A)} , ((opP xP zP) = (opP yP zP) → xP = yP)))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ca1 : (CancellativeCommutativeMonoid A1)) (Ca2 : (CancellativeCommutativeMonoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ca1) x1 x2)) = ((op Ca2) (hom x1) (hom x2))))
       (pres_e : (hom (e Ca1)) = (e Ca2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ca1 : (CancellativeCommutativeMonoid A1)) (Ca2 : (CancellativeCommutativeMonoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ca1) x1 x2) ((op Ca2) y1 y2))))))
       (interp_e : (interp (e Ca1) (e Ca2))) 
  
  inductive CancellativeCommutativeMonoidTerm   : Type  
     | opL : (CancellativeCommutativeMonoidTerm → (CancellativeCommutativeMonoidTerm → CancellativeCommutativeMonoidTerm)) 
     | eL : CancellativeCommutativeMonoidTerm  
      open CancellativeCommutativeMonoidTerm 
  
  inductive ClCancellativeCommutativeMonoidTerm  (A : Type) : Type  
     | sing : (A → ClCancellativeCommutativeMonoidTerm) 
     | opCl : (ClCancellativeCommutativeMonoidTerm → (ClCancellativeCommutativeMonoidTerm → ClCancellativeCommutativeMonoidTerm)) 
     | eCl : ClCancellativeCommutativeMonoidTerm  
      open ClCancellativeCommutativeMonoidTerm 
  
  inductive OpCancellativeCommutativeMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCancellativeCommutativeMonoidTerm) 
     | opOL : (OpCancellativeCommutativeMonoidTerm → (OpCancellativeCommutativeMonoidTerm → OpCancellativeCommutativeMonoidTerm)) 
     | eOL : OpCancellativeCommutativeMonoidTerm  
      open OpCancellativeCommutativeMonoidTerm 
  
  inductive OpCancellativeCommutativeMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCancellativeCommutativeMonoidTerm2) 
     | sing2 : (A → OpCancellativeCommutativeMonoidTerm2) 
     | opOL2 : (OpCancellativeCommutativeMonoidTerm2 → (OpCancellativeCommutativeMonoidTerm2 → OpCancellativeCommutativeMonoidTerm2)) 
     | eOL2 : OpCancellativeCommutativeMonoidTerm2  
      open OpCancellativeCommutativeMonoidTerm2 
  
  def simplifyCl   (A : Type)  : ((ClCancellativeCommutativeMonoidTerm A) → (ClCancellativeCommutativeMonoidTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x eCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpCancellativeCommutativeMonoidTerm n) → (OpCancellativeCommutativeMonoidTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x eOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpCancellativeCommutativeMonoidTerm2 n A) → (OpCancellativeCommutativeMonoidTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x eOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CancellativeCommutativeMonoid A) → (CancellativeCommutativeMonoidTerm → A)) 
  | Ca (opL x1 x2) := ((op Ca) (evalB Ca x1) (evalB Ca x2))  
  | Ca eL := (e Ca)  
  def evalCl   {A : Type}  : ((CancellativeCommutativeMonoid A) → ((ClCancellativeCommutativeMonoidTerm A) → A)) 
  | Ca (sing x1) := x1  
  | Ca (opCl x1 x2) := ((op Ca) (evalCl Ca x1) (evalCl Ca x2))  
  | Ca eCl := (e Ca)  
  def evalOpB   {A : Type} (n : ℕ)  : ((CancellativeCommutativeMonoid A) → ((vector A n) → ((OpCancellativeCommutativeMonoidTerm n) → A))) 
  | Ca vars (v x1) := (nth vars x1)  
  | Ca vars (opOL x1 x2) := ((op Ca) (evalOpB Ca vars x1) (evalOpB Ca vars x2))  
  | Ca vars eOL := (e Ca)  
  def evalOp   {A : Type} (n : ℕ)  : ((CancellativeCommutativeMonoid A) → ((vector A n) → ((OpCancellativeCommutativeMonoidTerm2 n A) → A))) 
  | Ca vars (v2 x1) := (nth vars x1)  
  | Ca vars (sing2 x1) := x1  
  | Ca vars (opOL2 x1 x2) := ((op Ca) (evalOp Ca vars x1) (evalOp Ca vars x2))  
  | Ca vars eOL2 := (e Ca)  
  def inductionB   (P : (CancellativeCommutativeMonoidTerm → Type))  : ((∀ (x1 x2 : CancellativeCommutativeMonoidTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : CancellativeCommutativeMonoidTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   (A : Type) (P : ((ClCancellativeCommutativeMonoidTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCancellativeCommutativeMonoidTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClCancellativeCommutativeMonoidTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   (n : ℕ) (P : ((OpCancellativeCommutativeMonoidTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCancellativeCommutativeMonoidTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpCancellativeCommutativeMonoidTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpCancellativeCommutativeMonoidTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCancellativeCommutativeMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpCancellativeCommutativeMonoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (CancellativeCommutativeMonoidTerm → (Staged CancellativeCommutativeMonoidTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   (A : Type)  : ((ClCancellativeCommutativeMonoidTerm A) → (Staged (ClCancellativeCommutativeMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   (n : ℕ)  : ((OpCancellativeCommutativeMonoidTerm n) → (Staged (OpCancellativeCommutativeMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpCancellativeCommutativeMonoidTerm2 n A) → (Staged (OpCancellativeCommutativeMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end CancellativeCommutativeMonoid