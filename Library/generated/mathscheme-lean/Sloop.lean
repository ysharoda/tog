import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Sloop   
  structure Sloop  (A : Type) : Type := 
       (e : A)
       (op : (A → (A → A)))
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x)))
       (antiAbsorbent : (∀ {x y : A} , (op x (op x y)) = y))
       (unipotence : (∀ {x : A} , (op x x) = e)) 
  
  open Sloop
  structure Sig  (AS : Type) : Type := 
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP)))
       (antiAbsorbentP : (∀ {xP yP : (Prod A A)} , (opP xP (opP xP yP)) = yP))
       (unipotenceP : (∀ {xP : (Prod A A)} , (opP xP xP) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Sl1 : (Sloop A1)) (Sl2 : (Sloop A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e : (hom (e Sl1)) = (e Sl2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Sl1) x1 x2)) = ((op Sl2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Sl1 : (Sloop A1)) (Sl2 : (Sloop A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e : (interp (e Sl1) (e Sl2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Sl1) x1 x2) ((op Sl2) y1 y2)))))) 
  
  inductive SloopLTerm   : Type  
     | eL : SloopLTerm 
     | opL : (SloopLTerm → (SloopLTerm → SloopLTerm))  
      open SloopLTerm 
  
  inductive ClSloopClTerm  (A : Type) : Type  
     | sing : (A → ClSloopClTerm) 
     | eCl : ClSloopClTerm 
     | opCl : (ClSloopClTerm → (ClSloopClTerm → ClSloopClTerm))  
      open ClSloopClTerm 
  
  inductive OpSloopOLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpSloopOLTerm) 
     | eOL : OpSloopOLTerm 
     | opOL : (OpSloopOLTerm → (OpSloopOLTerm → OpSloopOLTerm))  
      open OpSloopOLTerm 
  
  inductive OpSloopOL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpSloopOL2Term2) 
     | sing2 : (A → OpSloopOL2Term2) 
     | eOL2 : OpSloopOL2Term2 
     | opOL2 : (OpSloopOL2Term2 → (OpSloopOL2Term2 → OpSloopOL2Term2))  
      open OpSloopOL2Term2 
  
  def simplifyCl   (A : Type)  : ((ClSloopClTerm A) → (ClSloopClTerm A)) 
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpSloopOLTerm n) → (OpSloopOLTerm n)) 
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpSloopOL2Term2 n A) → (OpSloopOL2Term2 n A)) 
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Sloop A) → (SloopLTerm → A)) 
  | Sl eL := (e Sl)  
  | Sl (opL x1 x2) := ((op Sl) (evalB Sl x1) (evalB Sl x2))  
  def evalCl   {A : Type}  : ((Sloop A) → ((ClSloopClTerm A) → A)) 
  | Sl (sing x1) := x1  
  | Sl eCl := (e Sl)  
  | Sl (opCl x1 x2) := ((op Sl) (evalCl Sl x1) (evalCl Sl x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Sloop A) → ((vector A n) → ((OpSloopOLTerm n) → A))) 
  | Sl vars (v x1) := (nth vars x1)  
  | Sl vars eOL := (e Sl)  
  | Sl vars (opOL x1 x2) := ((op Sl) (evalOpB Sl vars x1) (evalOpB Sl vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Sloop A) → ((vector A n) → ((OpSloopOL2Term2 n A) → A))) 
  | Sl vars (v2 x1) := (nth vars x1)  
  | Sl vars (sing2 x1) := x1  
  | Sl vars eOL2 := (e Sl)  
  | Sl vars (opOL2 x1 x2) := ((op Sl) (evalOp Sl vars x1) (evalOp Sl vars x2))  
  def inductionB   (P : (SloopLTerm → Type))  : ((P eL) → ((∀ (x1 x2 : SloopLTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : SloopLTerm) , (P x)))) 
  | pel popl eL := pel  
  | pel popl (opL x1 x2) := (popl _ _ (inductionB pel popl x1) (inductionB pel popl x2))  
  def inductionCl   (A : Type) (P : ((ClSloopClTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P eCl) → ((∀ (x1 x2 : (ClSloopClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClSloopClTerm A)) , (P x))))) 
  | psing pecl popcl (sing x1) := (psing x1)  
  | psing pecl popcl eCl := pecl  
  | psing pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pecl popcl x1) (inductionCl psing pecl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpSloopOLTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P eOL) → ((∀ (x1 x2 : (OpSloopOLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpSloopOLTerm n)) , (P x))))) 
  | pv peol popol (v x1) := (pv x1)  
  | pv peol popol eOL := peol  
  | pv peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv peol popol x1) (inductionOpB pv peol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpSloopOL2Term2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P eOL2) → ((∀ (x1 x2 : (OpSloopOL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpSloopOL2Term2 n A)) , (P x)))))) 
  | pv2 psing2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 peol2 popol2 x1) (inductionOp pv2 psing2 peol2 popol2 x2))  
  def stageB  : (SloopLTerm → (Staged SloopLTerm))
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClSloopClTerm A) → (Staged (ClSloopClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpSloopOLTerm n) → (Staged (OpSloopOLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpSloopOL2Term2 n A) → (Staged (OpSloopOL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Sloop