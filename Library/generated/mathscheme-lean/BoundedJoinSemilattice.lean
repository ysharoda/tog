import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BoundedJoinSemilattice   
  structure BoundedJoinSemilattice  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x)) 
  
  open BoundedJoinSemilattice
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BoundedJoinSemilattice A1)) (Bo2 : (BoundedJoinSemilattice A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Bo1) x1 x2)) = ((plus Bo2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Bo1)) = (zero Bo2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BoundedJoinSemilattice A1)) (Bo2 : (BoundedJoinSemilattice A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Bo1) x1 x2) ((plus Bo2) y1 y2))))))
       (interp_zero : (interp (zero Bo1) (zero Bo2))) 
  
  inductive BoundedJoinSemilatticeTerm   : Type  
     | plusL : (BoundedJoinSemilatticeTerm → (BoundedJoinSemilatticeTerm → BoundedJoinSemilatticeTerm)) 
     | zeroL : BoundedJoinSemilatticeTerm  
      open BoundedJoinSemilatticeTerm 
  
  inductive ClBoundedJoinSemilatticeTerm  (A : Type) : Type  
     | sing : (A → ClBoundedJoinSemilatticeTerm) 
     | plusCl : (ClBoundedJoinSemilatticeTerm → (ClBoundedJoinSemilatticeTerm → ClBoundedJoinSemilatticeTerm)) 
     | zeroCl : ClBoundedJoinSemilatticeTerm  
      open ClBoundedJoinSemilatticeTerm 
  
  inductive OpBoundedJoinSemilatticeTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBoundedJoinSemilatticeTerm) 
     | plusOL : (OpBoundedJoinSemilatticeTerm → (OpBoundedJoinSemilatticeTerm → OpBoundedJoinSemilatticeTerm)) 
     | zeroOL : OpBoundedJoinSemilatticeTerm  
      open OpBoundedJoinSemilatticeTerm 
  
  inductive OpBoundedJoinSemilatticeTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBoundedJoinSemilatticeTerm2) 
     | sing2 : (A → OpBoundedJoinSemilatticeTerm2) 
     | plusOL2 : (OpBoundedJoinSemilatticeTerm2 → (OpBoundedJoinSemilatticeTerm2 → OpBoundedJoinSemilatticeTerm2)) 
     | zeroOL2 : OpBoundedJoinSemilatticeTerm2  
      open OpBoundedJoinSemilatticeTerm2 
  
  def simplifyCl   (A : Type)  : ((ClBoundedJoinSemilatticeTerm A) → (ClBoundedJoinSemilatticeTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpBoundedJoinSemilatticeTerm n) → (OpBoundedJoinSemilatticeTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpBoundedJoinSemilatticeTerm2 n A) → (OpBoundedJoinSemilatticeTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BoundedJoinSemilattice A) → (BoundedJoinSemilatticeTerm → A)) 
  | Bo (plusL x1 x2) := ((plus Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo zeroL := (zero Bo)  
  def evalCl   {A : Type}  : ((BoundedJoinSemilattice A) → ((ClBoundedJoinSemilatticeTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo (plusCl x1 x2) := ((plus Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo zeroCl := (zero Bo)  
  def evalOpB   {A : Type} (n : ℕ)  : ((BoundedJoinSemilattice A) → ((vector A n) → ((OpBoundedJoinSemilatticeTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars (plusOL x1 x2) := ((plus Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars zeroOL := (zero Bo)  
  def evalOp   {A : Type} (n : ℕ)  : ((BoundedJoinSemilattice A) → ((vector A n) → ((OpBoundedJoinSemilatticeTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars (plusOL2 x1 x2) := ((plus Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars zeroOL2 := (zero Bo)  
  def inductionB   (P : (BoundedJoinSemilatticeTerm → Type))  : ((∀ (x1 x2 : BoundedJoinSemilatticeTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → (∀ (x : BoundedJoinSemilatticeTerm) , (P x)))) 
  | pplusl p0l (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l x1) (inductionB pplusl p0l x2))  
  | pplusl p0l zeroL := p0l  
  def inductionCl   (A : Type) (P : ((ClBoundedJoinSemilatticeTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBoundedJoinSemilatticeTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → (∀ (x : (ClBoundedJoinSemilatticeTerm A)) , (P x))))) 
  | psing ppluscl p0cl (sing x1) := (psing x1)  
  | psing ppluscl p0cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl x1) (inductionCl psing ppluscl p0cl x2))  
  | psing ppluscl p0cl zeroCl := p0cl  
  def inductionOpB   (n : ℕ) (P : ((OpBoundedJoinSemilatticeTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBoundedJoinSemilatticeTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → (∀ (x : (OpBoundedJoinSemilatticeTerm n)) , (P x))))) 
  | pv pplusol p0ol (v x1) := (pv x1)  
  | pv pplusol p0ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol x1) (inductionOpB pv pplusol p0ol x2))  
  | pv pplusol p0ol zeroOL := p0ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpBoundedJoinSemilatticeTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBoundedJoinSemilatticeTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → (∀ (x : (OpBoundedJoinSemilatticeTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 p0ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 zeroOL2 := p0ol2  
  def stageB  : (BoundedJoinSemilatticeTerm → (Staged BoundedJoinSemilatticeTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  def stageCl   (A : Type)  : ((ClBoundedJoinSemilatticeTerm A) → (Staged (ClBoundedJoinSemilatticeTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  def stageOpB   (n : ℕ)  : ((OpBoundedJoinSemilatticeTerm n) → (Staged (OpBoundedJoinSemilatticeTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpBoundedJoinSemilatticeTerm2 n A) → (Staged (OpBoundedJoinSemilatticeTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A)) 
  
end BoundedJoinSemilattice