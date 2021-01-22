import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftMonoid   
  structure LeftMonoid  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (lunit_e : (∀ {x : A} , (op e x) = x))
       (associative_op : (∀ {x y z : A} , (op (op x y) z) = (op x (op y z)))) 
  
  open LeftMonoid
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (lunit_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = xP))
       (associative_opP : (∀ {xP yP zP : (Prod A A)} , (opP (opP xP yP) zP) = (opP xP (opP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftMonoid A1)) (Le2 : (LeftMonoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Le1) x1 x2)) = ((op Le2) (hom x1) (hom x2))))
       (pres_e : (hom (e Le1)) = (e Le2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftMonoid A1)) (Le2 : (LeftMonoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2))))))
       (interp_e : (interp (e Le1) (e Le2))) 
  
  inductive LeftMonoidTerm   : Type  
     | opL : (LeftMonoidTerm → (LeftMonoidTerm → LeftMonoidTerm)) 
     | eL : LeftMonoidTerm  
      open LeftMonoidTerm 
  
  inductive ClLeftMonoidTerm  (A : Type) : Type  
     | sing : (A → ClLeftMonoidTerm) 
     | opCl : (ClLeftMonoidTerm → (ClLeftMonoidTerm → ClLeftMonoidTerm)) 
     | eCl : ClLeftMonoidTerm  
      open ClLeftMonoidTerm 
  
  inductive OpLeftMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftMonoidTerm) 
     | opOL : (OpLeftMonoidTerm → (OpLeftMonoidTerm → OpLeftMonoidTerm)) 
     | eOL : OpLeftMonoidTerm  
      open OpLeftMonoidTerm 
  
  inductive OpLeftMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftMonoidTerm2) 
     | sing2 : (A → OpLeftMonoidTerm2) 
     | opOL2 : (OpLeftMonoidTerm2 → (OpLeftMonoidTerm2 → OpLeftMonoidTerm2)) 
     | eOL2 : OpLeftMonoidTerm2  
      open OpLeftMonoidTerm2 
  
  def simplifyCl   {A : Type}  : ((ClLeftMonoidTerm A) → (ClLeftMonoidTerm A)) 
  | (opCl eCl x) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLeftMonoidTerm n) → (OpLeftMonoidTerm n)) 
  | (opOL eOL x) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLeftMonoidTerm2 n A) → (OpLeftMonoidTerm2 n A)) 
  | (opOL2 eOL2 x) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftMonoid A) → (LeftMonoidTerm → A)) 
  | Le (opL x1 x2) := ((op Le) (evalB Le x1) (evalB Le x2))  
  | Le eL := (e Le)  
  def evalCl   {A : Type}  : ((LeftMonoid A) → ((ClLeftMonoidTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (opCl x1 x2) := ((op Le) (evalCl Le x1) (evalCl Le x2))  
  | Le eCl := (e Le)  
  def evalOpB   {A : Type} {n : ℕ}  : ((LeftMonoid A) → ((vector A n) → ((OpLeftMonoidTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (opOL x1 x2) := ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  | Le vars eOL := (e Le)  
  def evalOp   {A : Type} {n : ℕ}  : ((LeftMonoid A) → ((vector A n) → ((OpLeftMonoidTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (opOL2 x1 x2) := ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  | Le vars eOL2 := (e Le)  
  def inductionB   {P : (LeftMonoidTerm → Type)}  : ((∀ (x1 x2 : LeftMonoidTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : LeftMonoidTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClLeftMonoidTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftMonoidTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClLeftMonoidTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpLeftMonoidTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftMonoidTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpLeftMonoidTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLeftMonoidTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpLeftMonoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (LeftMonoidTerm → (Staged LeftMonoidTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClLeftMonoidTerm A) → (Staged (ClLeftMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpLeftMonoidTerm n) → (Staged (OpLeftMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLeftMonoidTerm2 n A) → (Staged (OpLeftMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end LeftMonoid