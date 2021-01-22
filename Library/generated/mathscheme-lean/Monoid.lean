import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Monoid   
  structure Monoid  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (runit_e : (∀ {x : A} , (op x e) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z)))) 
  
  open Monoid
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mo1 : (Monoid A1)) (Mo2 : (Monoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Mo1) x1 x2)) = ((op Mo2) (hom x1) (hom x2))))
       (pres_e : (hom (e Mo1)) = (e Mo2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mo1 : (Monoid A1)) (Mo2 : (Monoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Mo1) x1 x2) ((op Mo2) y1 y2))))))
       (interp_e : (interp (e Mo1) (e Mo2))) 
  
  inductive MonoidTerm   : Type  
     | opL : (MonoidTerm → (MonoidTerm → MonoidTerm)) 
     | eL : MonoidTerm  
      open MonoidTerm 
  
  inductive ClMonoidTerm  (A : Type) : Type  
     | sing : (A → ClMonoidTerm) 
     | opCl : (ClMonoidTerm → (ClMonoidTerm → ClMonoidTerm)) 
     | eCl : ClMonoidTerm  
      open ClMonoidTerm 
  
  inductive OpMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMonoidTerm) 
     | opOL : (OpMonoidTerm → (OpMonoidTerm → OpMonoidTerm)) 
     | eOL : OpMonoidTerm  
      open OpMonoidTerm 
  
  inductive OpMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMonoidTerm2) 
     | sing2 : (A → OpMonoidTerm2) 
     | opOL2 : (OpMonoidTerm2 → (OpMonoidTerm2 → OpMonoidTerm2)) 
     | eOL2 : OpMonoidTerm2  
      open OpMonoidTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMonoidTerm A) → (ClMonoidTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x eCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMonoidTerm n) → (OpMonoidTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x eOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMonoidTerm2 n A) → (OpMonoidTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x eOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Monoid A) → (MonoidTerm → A)) 
  | Mo (opL x1 x2) := ((op Mo) (evalB Mo x1) (evalB Mo x2))  
  | Mo eL := (e Mo)  
  def evalCl   {A : Type}  : ((Monoid A) → ((ClMonoidTerm A) → A)) 
  | Mo (sing x1) := x1  
  | Mo (opCl x1 x2) := ((op Mo) (evalCl Mo x1) (evalCl Mo x2))  
  | Mo eCl := (e Mo)  
  def evalOpB   {A : Type} {n : ℕ}  : ((Monoid A) → ((vector A n) → ((OpMonoidTerm n) → A))) 
  | Mo vars (v x1) := (nth vars x1)  
  | Mo vars (opOL x1 x2) := ((op Mo) (evalOpB Mo vars x1) (evalOpB Mo vars x2))  
  | Mo vars eOL := (e Mo)  
  def evalOp   {A : Type} {n : ℕ}  : ((Monoid A) → ((vector A n) → ((OpMonoidTerm2 n A) → A))) 
  | Mo vars (v2 x1) := (nth vars x1)  
  | Mo vars (sing2 x1) := x1  
  | Mo vars (opOL2 x1 x2) := ((op Mo) (evalOp Mo vars x1) (evalOp Mo vars x2))  
  | Mo vars eOL2 := (e Mo)  
  def inductionB   {P : (MonoidTerm → Type)}  : ((∀ (x1 x2 : MonoidTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : MonoidTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClMonoidTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMonoidTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClMonoidTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpMonoidTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMonoidTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpMonoidTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMonoidTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpMonoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (MonoidTerm → (Staged MonoidTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClMonoidTerm A) → (Staged (ClMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpMonoidTerm n) → (Staged (OpMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMonoidTerm2 n A) → (Staged (OpMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end Monoid