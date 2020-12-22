import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section JoinSemilattice   
  structure JoinSemilattice  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x)) 
  
  open JoinSemilattice
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Jo1 : (JoinSemilattice A1)) (Jo2 : (JoinSemilattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Jo1) x1 x2)) = ((plus Jo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Jo1 : (JoinSemilattice A1)) (Jo2 : (JoinSemilattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Jo1) x1 x2) ((plus Jo2) y1 y2)))))) 
  
  inductive JoinSemilatticeTerm   : Type  
     | plusL : (JoinSemilatticeTerm → (JoinSemilatticeTerm → JoinSemilatticeTerm))  
      open JoinSemilatticeTerm 
  
  inductive ClJoinSemilatticeTerm  (A : Type) : Type  
     | sing : (A → ClJoinSemilatticeTerm) 
     | plusCl : (ClJoinSemilatticeTerm → (ClJoinSemilatticeTerm → ClJoinSemilatticeTerm))  
      open ClJoinSemilatticeTerm 
  
  inductive OpJoinSemilatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpJoinSemilatticeTerm) 
     | plusOL : (OpJoinSemilatticeTerm → (OpJoinSemilatticeTerm → OpJoinSemilatticeTerm))  
      open OpJoinSemilatticeTerm 
  
  inductive OpJoinSemilatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpJoinSemilatticeTerm2) 
     | sing2 : (A → OpJoinSemilatticeTerm2) 
     | plusOL2 : (OpJoinSemilatticeTerm2 → (OpJoinSemilatticeTerm2 → OpJoinSemilatticeTerm2))  
      open OpJoinSemilatticeTerm2 
  
  def simplifyCl   (A : Type)  : ((ClJoinSemilatticeTerm A) → (ClJoinSemilatticeTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpJoinSemilatticeTerm n) → (OpJoinSemilatticeTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpJoinSemilatticeTerm2 n A) → (OpJoinSemilatticeTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((JoinSemilattice A) → (JoinSemilatticeTerm → A)) 
  | Jo (plusL x1 x2) := ((plus Jo) (evalB Jo x1) (evalB Jo x2))  
  def evalCl   {A : Type}  : ((JoinSemilattice A) → ((ClJoinSemilatticeTerm A) → A)) 
  | Jo (sing x1) := x1  
  | Jo (plusCl x1 x2) := ((plus Jo) (evalCl Jo x1) (evalCl Jo x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((JoinSemilattice A) → ((vector A n) → ((OpJoinSemilatticeTerm n) → A))) 
  | Jo vars (v x1) := (nth vars x1)  
  | Jo vars (plusOL x1 x2) := ((plus Jo) (evalOpB Jo vars x1) (evalOpB Jo vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((JoinSemilattice A) → ((vector A n) → ((OpJoinSemilatticeTerm2 n A) → A))) 
  | Jo vars (v2 x1) := (nth vars x1)  
  | Jo vars (sing2 x1) := x1  
  | Jo vars (plusOL2 x1 x2) := ((plus Jo) (evalOp Jo vars x1) (evalOp Jo vars x2))  
  def inductionB   (P : (JoinSemilatticeTerm → Type))  : ((∀ (x1 x2 : JoinSemilatticeTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : JoinSemilatticeTerm) , (P x))) 
  | pplusl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl x1) (inductionB pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClJoinSemilatticeTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClJoinSemilatticeTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClJoinSemilatticeTerm A)) , (P x)))) 
  | psing ppluscl (sing x1) := (psing x1)  
  | psing ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl x1) (inductionCl psing ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpJoinSemilatticeTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpJoinSemilatticeTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpJoinSemilatticeTerm n)) , (P x)))) 
  | pv pplusol (v x1) := (pv x1)  
  | pv pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol x1) (inductionOpB pv pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpJoinSemilatticeTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpJoinSemilatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpJoinSemilatticeTerm2 n A)) , (P x))))) 
  | pv2 psing2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 x1) (inductionOp pv2 psing2 pplusol2 x2))  
  def stageB  : (JoinSemilatticeTerm → (Staged JoinSemilatticeTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClJoinSemilatticeTerm A) → (Staged (ClJoinSemilatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpJoinSemilatticeTerm n) → (Staged (OpJoinSemilatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpJoinSemilatticeTerm2 n A) → (Staged (OpJoinSemilatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end JoinSemilattice