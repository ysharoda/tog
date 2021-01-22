import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftZero   
  structure LeftZero  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (leftZero_op_e : (∀ {x : A} , (op e x) = e)) 
  
  open LeftZero
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftZero_op_eP : (∀ {xP : (Prod A A)} , (opP eP xP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftZero A1)) (Le2 : (LeftZero A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Le1)) = (e Le2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Le1) x1 x2)) = ((op Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftZero A1)) (Le2 : (LeftZero A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Le1) (e Le2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))) 
  
  inductive LeftZeroTerm   : Type  
     | eL : LeftZeroTerm 
     | opL : (LeftZeroTerm → (LeftZeroTerm → LeftZeroTerm))  
      open LeftZeroTerm 
  
  inductive ClLeftZeroTerm  (A : Type) : Type  
     | sing : (A → ClLeftZeroTerm) 
     | eCl : ClLeftZeroTerm 
     | opCl : (ClLeftZeroTerm → (ClLeftZeroTerm → ClLeftZeroTerm))  
      open ClLeftZeroTerm 
  
  inductive OpLeftZeroTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftZeroTerm) 
     | eOL : OpLeftZeroTerm 
     | opOL : (OpLeftZeroTerm → (OpLeftZeroTerm → OpLeftZeroTerm))  
      open OpLeftZeroTerm 
  
  inductive OpLeftZeroTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftZeroTerm2) 
     | sing2 : (A → OpLeftZeroTerm2) 
     | eOL2 : OpLeftZeroTerm2 
     | opOL2 : (OpLeftZeroTerm2 → (OpLeftZeroTerm2 → OpLeftZeroTerm2))  
      open OpLeftZeroTerm2 
  
  def simplifyCl   {A : Type}  : ((ClLeftZeroTerm A) → (ClLeftZeroTerm A)) 
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLeftZeroTerm n) → (OpLeftZeroTerm n)) 
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLeftZeroTerm2 n A) → (OpLeftZeroTerm2 n A)) 
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftZero A) → (LeftZeroTerm → A)) 
  | Le eL := (e Le)  
  | Le (opL x1 x2) := ((op Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftZero A) → ((ClLeftZeroTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le eCl := (e Le)  
  | Le (opCl x1 x2) := ((op Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((LeftZero A) → ((vector A n) → ((OpLeftZeroTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars eOL := (e Le)  
  | Le vars (opOL x1 x2) := ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((LeftZero A) → ((vector A n) → ((OpLeftZeroTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars eOL2 := (e Le)  
  | Le vars (opOL2 x1 x2) := ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   {P : (LeftZeroTerm → Type)}  : ((P eL) → ((∀ (x1 x2 : LeftZeroTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : LeftZeroTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   {A : Type} {P : ((ClLeftZeroTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClLeftZeroTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClLeftZeroTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpLeftZeroTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpLeftZeroTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpLeftZeroTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLeftZeroTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpLeftZeroTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpLeftZeroTerm2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (LeftZeroTerm → (Staged LeftZeroTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClLeftZeroTerm A) → (Staged (ClLeftZeroTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpLeftZeroTerm n) → (Staged (OpLeftZeroTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLeftZeroTerm2 n A) → (Staged (OpLeftZeroTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftZero