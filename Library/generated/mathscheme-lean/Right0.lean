import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Right0   
  structure Right0  (A : Type) : Type := 
       (zero : A)
       (op : (A → (A → A)))
       (rightZero_op_zero : (∀ {x : A} , (op x zero) = zero)) 
  
  open Right0
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (opP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (Right0 A1)) (Ri2 : (Right0 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ri1)) = (zero Ri2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Ri1) x1 x2)) = ((op Ri2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (Right0 A1)) (Ri2 : (Right0 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ri1) (zero Ri2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Ri1) x1 x2) ((op Ri2) y1 y2)))))) 
  
  inductive Right0LTerm   : Type  
     | zeroL : Right0LTerm 
     | opL : (Right0LTerm → (Right0LTerm → Right0LTerm))  
      open Right0LTerm 
  
  inductive ClRight0ClTerm  (A : Type) : Type  
     | sing : (A → ClRight0ClTerm) 
     | zeroCl : ClRight0ClTerm 
     | opCl : (ClRight0ClTerm → (ClRight0ClTerm → ClRight0ClTerm))  
      open ClRight0ClTerm 
  
  inductive OpRight0OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRight0OLTerm) 
     | zeroOL : OpRight0OLTerm 
     | opOL : (OpRight0OLTerm → (OpRight0OLTerm → OpRight0OLTerm))  
      open OpRight0OLTerm 
  
  inductive OpRight0OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRight0OL2Term2) 
     | sing2 : (A → OpRight0OL2Term2) 
     | zeroOL2 : OpRight0OL2Term2 
     | opOL2 : (OpRight0OL2Term2 → (OpRight0OL2Term2 → OpRight0OL2Term2))  
      open OpRight0OL2Term2 
  
  def simplifyCl   {A : Type}  : ((ClRight0ClTerm A) → (ClRight0ClTerm A)) 
  | zeroCl := zeroCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpRight0OLTerm n) → (OpRight0OLTerm n)) 
  | zeroOL := zeroOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpRight0OL2Term2 n A) → (OpRight0OL2Term2 n A)) 
  | zeroOL2 := zeroOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Right0 A) → (Right0LTerm → A)) 
  | Ri zeroL := (zero Ri)  
  | Ri (opL x1 x2) := ((op Ri) (evalB Ri x1) (evalB Ri x2))  
  def evalCl   {A : Type}  : ((Right0 A) → ((ClRight0ClTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri zeroCl := (zero Ri)  
  | Ri (opCl x1 x2) := ((op Ri) (evalCl Ri x1) (evalCl Ri x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((Right0 A) → ((vector A n) → ((OpRight0OLTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars zeroOL := (zero Ri)  
  | Ri vars (opOL x1 x2) := ((op Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((Right0 A) → ((vector A n) → ((OpRight0OL2Term2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars zeroOL2 := (zero Ri)  
  | Ri vars (opOL2 x1 x2) := ((op Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  def inductionB   {P : (Right0LTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : Right0LTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : Right0LTerm) , (P x)))) 
  | p0l popl zeroL := p0l  
  | p0l popl (opL x1 x2) := (popl _ _ (inductionB p0l popl x1) (inductionB p0l popl x2))  
  def inductionCl   {A : Type} {P : ((ClRight0ClTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClRight0ClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClRight0ClTerm A)) , (P x))))) 
  | psing p0cl popcl (sing x1) := (psing x1)  
  | psing p0cl popcl zeroCl := p0cl  
  | psing p0cl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing p0cl popcl x1) (inductionCl psing p0cl popcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpRight0OLTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpRight0OLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpRight0OLTerm n)) , (P x))))) 
  | pv p0ol popol (v x1) := (pv x1)  
  | pv p0ol popol zeroOL := p0ol  
  | pv p0ol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv p0ol popol x1) (inductionOpB pv p0ol popol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpRight0OL2Term2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpRight0OL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpRight0OL2Term2 n A)) , (P x)))))) 
  | pv2 psing2 p0ol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 popol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 p0ol2 popol2 x1) (inductionOp pv2 psing2 p0ol2 popol2 x2))  
  def stageB  : (Right0LTerm → (Staged Right0LTerm))
  | zeroL := (Now zeroL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClRight0ClTerm A) → (Staged (ClRight0ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpRight0OLTerm n) → (Staged (OpRight0OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpRight0OL2Term2 n A) → (Staged (OpRight0OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Right0