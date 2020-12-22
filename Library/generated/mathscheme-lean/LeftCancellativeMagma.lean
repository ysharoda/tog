import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftCancellativeMagma   
  structure LeftCancellativeMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (leftCancellative : (∀ {x y z : A} , ((op z x) = (op z y) → x = y))) 
  
  open LeftCancellativeMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftCancellativeP : (∀ {xP yP zP : (Prod A A)} , ((opP zP xP) = (opP zP yP) → xP = yP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftCancellativeMagma A1)) (Le2 : (LeftCancellativeMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Le1) x1 x2)) = ((op Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftCancellativeMagma A1)) (Le2 : (LeftCancellativeMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))) 
  
  inductive LeftCancellativeMagmaTerm   : Type  
     | opL : (LeftCancellativeMagmaTerm → (LeftCancellativeMagmaTerm → LeftCancellativeMagmaTerm))  
      open LeftCancellativeMagmaTerm 
  
  inductive ClLeftCancellativeMagmaTerm  (A : Type) : Type  
     | sing : (A → ClLeftCancellativeMagmaTerm) 
     | opCl : (ClLeftCancellativeMagmaTerm → (ClLeftCancellativeMagmaTerm → ClLeftCancellativeMagmaTerm))  
      open ClLeftCancellativeMagmaTerm 
  
  inductive OpLeftCancellativeMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftCancellativeMagmaTerm) 
     | opOL : (OpLeftCancellativeMagmaTerm → (OpLeftCancellativeMagmaTerm → OpLeftCancellativeMagmaTerm))  
      open OpLeftCancellativeMagmaTerm 
  
  inductive OpLeftCancellativeMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftCancellativeMagmaTerm2) 
     | sing2 : (A → OpLeftCancellativeMagmaTerm2) 
     | opOL2 : (OpLeftCancellativeMagmaTerm2 → (OpLeftCancellativeMagmaTerm2 → OpLeftCancellativeMagmaTerm2))  
      open OpLeftCancellativeMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClLeftCancellativeMagmaTerm A) → (ClLeftCancellativeMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpLeftCancellativeMagmaTerm n) → (OpLeftCancellativeMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpLeftCancellativeMagmaTerm2 n A) → (OpLeftCancellativeMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftCancellativeMagma A) → (LeftCancellativeMagmaTerm → A)) 
  | Le (opL x1 x2) := ((op Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftCancellativeMagma A) → ((ClLeftCancellativeMagmaTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (opCl x1 x2) := ((op Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((LeftCancellativeMagma A) → ((vector A n) → ((OpLeftCancellativeMagmaTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (opOL x1 x2) := ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((LeftCancellativeMagma A) → ((vector A n) → ((OpLeftCancellativeMagmaTerm2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (opOL2 x1 x2) := ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   (P : (LeftCancellativeMagmaTerm → Type))  : ((∀ (x1 x2 : LeftCancellativeMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : LeftCancellativeMagmaTerm) , (P x))) 
  | popl (opL x1 x2) := (popl _ _ (inductionB popl x1) (inductionB popl x2))  
  def inductionCl   (A : Type) (P : ((ClLeftCancellativeMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftCancellativeMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClLeftCancellativeMagmaTerm A)) , (P x)))) 
  | psing popcl (sing x1) := (psing x1)  
  | psing popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl x1) (inductionCl psing popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpLeftCancellativeMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftCancellativeMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpLeftCancellativeMagmaTerm n)) , (P x)))) 
  | pv popol (v x1) := (pv x1)  
  | pv popol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol x1) (inductionOpB pv popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpLeftCancellativeMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftCancellativeMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpLeftCancellativeMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 x1) (inductionOp pv2 psing2 popol2 x2))  
  def stageB  : (LeftCancellativeMagmaTerm → (Staged LeftCancellativeMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClLeftCancellativeMagmaTerm A) → (Staged (ClLeftCancellativeMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpLeftCancellativeMagmaTerm n) → (Staged (OpLeftCancellativeMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpLeftCancellativeMagmaTerm2 n A) → (Staged (OpLeftCancellativeMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftCancellativeMagma