import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Left0   
  structure Left0  (A : Type) : Type := 
       (zero : A)
       (op : (A → (A → A)))
       (leftZero_op_zero : (∀ {x : A} , (op zero x) = zero)) 
  
  open Left0
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (opP zeroP xP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (Left0 A1)) (Le2 : (Left0 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Le1)) = (zero Le2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Le1) x1 x2)) = ((op Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (Left0 A1)) (Le2 : (Left0 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Le1) (zero Le2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))) 
  
  inductive Left0LTerm   : Type  
     | zeroL : Left0LTerm 
     | opL : (Left0LTerm → (Left0LTerm → Left0LTerm))  
      open Left0LTerm 
  
  inductive ClLeft0ClTerm  (A : Type) : Type  
     | sing : (A → ClLeft0ClTerm) 
     | zeroCl : ClLeft0ClTerm 
     | opCl : (ClLeft0ClTerm → (ClLeft0ClTerm → ClLeft0ClTerm))  
      open ClLeft0ClTerm 
  
  inductive OpLeft0OLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeft0OLTerm) 
     | zeroOL : OpLeft0OLTerm 
     | opOL : (OpLeft0OLTerm → (OpLeft0OLTerm → OpLeft0OLTerm))  
      open OpLeft0OLTerm 
  
  inductive OpLeft0OL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeft0OL2Term2) 
     | sing2 : (A → OpLeft0OL2Term2) 
     | zeroOL2 : OpLeft0OL2Term2 
     | opOL2 : (OpLeft0OL2Term2 → (OpLeft0OL2Term2 → OpLeft0OL2Term2))  
      open OpLeft0OL2Term2 
  
  def simplifyCl   (A : Type)  : ((ClLeft0ClTerm A) → (ClLeft0ClTerm A)) 
  | zeroCl := zeroCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpLeft0OLTerm n) → (OpLeft0OLTerm n)) 
  | zeroOL := zeroOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpLeft0OL2Term2 n A) → (OpLeft0OL2Term2 n A)) 
  | zeroOL2 := zeroOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Left0 A) → (Left0LTerm → A)) 
  | Le zeroL := (zero Le)  
  | Le (opL x1 x2) := ((op Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((Left0 A) → ((ClLeft0ClTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le zeroCl := (zero Le)  
  | Le (opCl x1 x2) := ((op Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Left0 A) → ((vector A n) → ((OpLeft0OLTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars zeroOL := (zero Le)  
  | Le vars (opOL x1 x2) := ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Left0 A) → ((vector A n) → ((OpLeft0OL2Term2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars zeroOL2 := (zero Le)  
  | Le vars (opOL2 x1 x2) := ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   (P : (Left0LTerm → Type))  : ((P zeroL) → ((∀ (x1 x2 : Left0LTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : Left0LTerm) , (P x)))) 
  | p0l popl zeroL := p0l  
  | p0l popl (opL x1 x2) := (popl _ _ (inductionB p0l popl x1) (inductionB p0l popl x2))  
  def inductionCl   (A : Type) (P : ((ClLeft0ClTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClLeft0ClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClLeft0ClTerm A)) , (P x))))) 
  | psing p0cl popcl (sing x1) := (psing x1)  
  | psing p0cl popcl zeroCl := p0cl  
  | psing p0cl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing p0cl popcl x1) (inductionCl psing p0cl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpLeft0OLTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpLeft0OLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpLeft0OLTerm n)) , (P x))))) 
  | pv p0ol popol (v x1) := (pv x1)  
  | pv p0ol popol zeroOL := p0ol  
  | pv p0ol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv p0ol popol x1) (inductionOpB pv p0ol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpLeft0OL2Term2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpLeft0OL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpLeft0OL2Term2 n A)) , (P x)))))) 
  | pv2 psing2 p0ol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 popol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 p0ol2 popol2 x1) (inductionOp pv2 psing2 p0ol2 popol2 x2))  
  def stageB  : (Left0LTerm → (Staged Left0LTerm))
  | zeroL := (Now zeroL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClLeft0ClTerm A) → (Staged (ClLeft0ClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpLeft0OLTerm n) → (Staged (OpLeft0OLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpLeft0OL2Term2 n A) → (Staged (OpLeft0OL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Left0