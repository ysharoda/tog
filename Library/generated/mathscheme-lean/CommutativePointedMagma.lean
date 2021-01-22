import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CommutativePointedMagma   
  structure CommutativePointedMagma  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (commutative_op : (∀ {x y : A} , (op x y) = (op y x))) 
  
  open CommutativePointedMagma
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (commutative_opP : (∀ {xP yP : (Prod A A)} , (opP xP yP) = (opP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (CommutativePointedMagma A1)) (Co2 : (CommutativePointedMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Co1) x1 x2)) = ((op Co2) (hom x1) (hom x2))))
       (pres_e : (hom (e Co1)) = (e Co2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (CommutativePointedMagma A1)) (Co2 : (CommutativePointedMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Co1) x1 x2) ((op Co2) y1 y2))))))
       (interp_e : (interp (e Co1) (e Co2))) 
  
  inductive CommutativePointedMagmaTerm   : Type  
     | opL : (CommutativePointedMagmaTerm → (CommutativePointedMagmaTerm → CommutativePointedMagmaTerm)) 
     | eL : CommutativePointedMagmaTerm  
      open CommutativePointedMagmaTerm 
  
  inductive ClCommutativePointedMagmaTerm  (A : Type) : Type  
     | sing : (A → ClCommutativePointedMagmaTerm) 
     | opCl : (ClCommutativePointedMagmaTerm → (ClCommutativePointedMagmaTerm → ClCommutativePointedMagmaTerm)) 
     | eCl : ClCommutativePointedMagmaTerm  
      open ClCommutativePointedMagmaTerm 
  
  inductive OpCommutativePointedMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCommutativePointedMagmaTerm) 
     | opOL : (OpCommutativePointedMagmaTerm → (OpCommutativePointedMagmaTerm → OpCommutativePointedMagmaTerm)) 
     | eOL : OpCommutativePointedMagmaTerm  
      open OpCommutativePointedMagmaTerm 
  
  inductive OpCommutativePointedMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCommutativePointedMagmaTerm2) 
     | sing2 : (A → OpCommutativePointedMagmaTerm2) 
     | opOL2 : (OpCommutativePointedMagmaTerm2 → (OpCommutativePointedMagmaTerm2 → OpCommutativePointedMagmaTerm2)) 
     | eOL2 : OpCommutativePointedMagmaTerm2  
      open OpCommutativePointedMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClCommutativePointedMagmaTerm A) → (ClCommutativePointedMagmaTerm A)) 
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpCommutativePointedMagmaTerm n) → (OpCommutativePointedMagmaTerm n)) 
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpCommutativePointedMagmaTerm2 n A) → (OpCommutativePointedMagmaTerm2 n A)) 
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CommutativePointedMagma A) → (CommutativePointedMagmaTerm → A)) 
  | Co (opL x1 x2) := ((op Co) (evalB Co x1) (evalB Co x2))  
  | Co eL := (e Co)  
  def evalCl   {A : Type}  : ((CommutativePointedMagma A) → ((ClCommutativePointedMagmaTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co (opCl x1 x2) := ((op Co) (evalCl Co x1) (evalCl Co x2))  
  | Co eCl := (e Co)  
  def evalOpB   {A : Type} {n : ℕ}  : ((CommutativePointedMagma A) → ((vector A n) → ((OpCommutativePointedMagmaTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars (opOL x1 x2) := ((op Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  | Co vars eOL := (e Co)  
  def evalOp   {A : Type} {n : ℕ}  : ((CommutativePointedMagma A) → ((vector A n) → ((OpCommutativePointedMagmaTerm2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars (opOL2 x1 x2) := ((op Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  | Co vars eOL2 := (e Co)  
  def inductionB   {P : (CommutativePointedMagmaTerm → Type)}  : ((∀ (x1 x2 : CommutativePointedMagmaTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → (∀ (x : CommutativePointedMagmaTerm) , (P x)))) 
  | popl pel (opL x1 x2) := (popl _ _ (inductionB popl pel x1) (inductionB popl pel x2))  
  | popl pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClCommutativePointedMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCommutativePointedMagmaTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → (∀ (x : (ClCommutativePointedMagmaTerm A)) , (P x))))) 
  | psing popcl pecl (sing x1) := (psing x1)  
  | psing popcl pecl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl x1) (inductionCl psing popcl pecl x2))  
  | psing popcl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpCommutativePointedMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCommutativePointedMagmaTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → (∀ (x : (OpCommutativePointedMagmaTerm n)) , (P x))))) 
  | pv popol peol (v x1) := (pv x1)  
  | pv popol peol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol x1) (inductionOpB pv popol peol x2))  
  | pv popol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpCommutativePointedMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCommutativePointedMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpCommutativePointedMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 popol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 x1) (inductionOp pv2 psing2 popol2 peol2 x2))  
  | pv2 psing2 popol2 peol2 eOL2 := peol2  
  def stageB  : (CommutativePointedMagmaTerm → (Staged CommutativePointedMagmaTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClCommutativePointedMagmaTerm A) → (Staged (ClCommutativePointedMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpCommutativePointedMagmaTerm n) → (Staged (OpCommutativePointedMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpCommutativePointedMagmaTerm2 n A) → (Staged (OpCommutativePointedMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end CommutativePointedMagma