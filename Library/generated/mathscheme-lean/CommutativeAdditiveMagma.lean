import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CommutativeAdditiveMagma   
  structure CommutativeAdditiveMagma  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x))) 
  
  open CommutativeAdditiveMagma
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (CommutativeAdditiveMagma A1)) (Co2 : (CommutativeAdditiveMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Co1) x1 x2)) = ((plus Co2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (CommutativeAdditiveMagma A1)) (Co2 : (CommutativeAdditiveMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Co1) x1 x2) ((plus Co2) y1 y2)))))) 
  
  inductive CommutativeAdditiveMagmaTerm   : Type  
     | plusL : (CommutativeAdditiveMagmaTerm → (CommutativeAdditiveMagmaTerm → CommutativeAdditiveMagmaTerm))  
      open CommutativeAdditiveMagmaTerm 
  
  inductive ClCommutativeAdditiveMagmaTerm  (A : Type) : Type  
     | sing : (A → ClCommutativeAdditiveMagmaTerm) 
     | plusCl : (ClCommutativeAdditiveMagmaTerm → (ClCommutativeAdditiveMagmaTerm → ClCommutativeAdditiveMagmaTerm))  
      open ClCommutativeAdditiveMagmaTerm 
  
  inductive OpCommutativeAdditiveMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCommutativeAdditiveMagmaTerm) 
     | plusOL : (OpCommutativeAdditiveMagmaTerm → (OpCommutativeAdditiveMagmaTerm → OpCommutativeAdditiveMagmaTerm))  
      open OpCommutativeAdditiveMagmaTerm 
  
  inductive OpCommutativeAdditiveMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCommutativeAdditiveMagmaTerm2) 
     | sing2 : (A → OpCommutativeAdditiveMagmaTerm2) 
     | plusOL2 : (OpCommutativeAdditiveMagmaTerm2 → (OpCommutativeAdditiveMagmaTerm2 → OpCommutativeAdditiveMagmaTerm2))  
      open OpCommutativeAdditiveMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClCommutativeAdditiveMagmaTerm A) → (ClCommutativeAdditiveMagmaTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpCommutativeAdditiveMagmaTerm n) → (OpCommutativeAdditiveMagmaTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpCommutativeAdditiveMagmaTerm2 n A) → (OpCommutativeAdditiveMagmaTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CommutativeAdditiveMagma A) → (CommutativeAdditiveMagmaTerm → A)) 
  | Co (plusL x1 x2) := ((plus Co) (evalB Co x1) (evalB Co x2))  
  def evalCl   {A : Type}  : ((CommutativeAdditiveMagma A) → ((ClCommutativeAdditiveMagmaTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co (plusCl x1 x2) := ((plus Co) (evalCl Co x1) (evalCl Co x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((CommutativeAdditiveMagma A) → ((vector A n) → ((OpCommutativeAdditiveMagmaTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars (plusOL x1 x2) := ((plus Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((CommutativeAdditiveMagma A) → ((vector A n) → ((OpCommutativeAdditiveMagmaTerm2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars (plusOL2 x1 x2) := ((plus Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  def inductionB   (P : (CommutativeAdditiveMagmaTerm → Type))  : ((∀ (x1 x2 : CommutativeAdditiveMagmaTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : CommutativeAdditiveMagmaTerm) , (P x))) 
  | pplusl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl x1) (inductionB pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClCommutativeAdditiveMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClCommutativeAdditiveMagmaTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClCommutativeAdditiveMagmaTerm A)) , (P x)))) 
  | psing ppluscl (sing x1) := (psing x1)  
  | psing ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl x1) (inductionCl psing ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpCommutativeAdditiveMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpCommutativeAdditiveMagmaTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpCommutativeAdditiveMagmaTerm n)) , (P x)))) 
  | pv pplusol (v x1) := (pv x1)  
  | pv pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol x1) (inductionOpB pv pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpCommutativeAdditiveMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpCommutativeAdditiveMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpCommutativeAdditiveMagmaTerm2 n A)) , (P x))))) 
  | pv2 psing2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 x1) (inductionOp pv2 psing2 pplusol2 x2))  
  def stageB  : (CommutativeAdditiveMagmaTerm → (Staged CommutativeAdditiveMagmaTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClCommutativeAdditiveMagmaTerm A) → (Staged (ClCommutativeAdditiveMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpCommutativeAdditiveMagmaTerm n) → (Staged (OpCommutativeAdditiveMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpCommutativeAdditiveMagmaTerm2 n A) → (Staged (OpCommutativeAdditiveMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end CommutativeAdditiveMagma