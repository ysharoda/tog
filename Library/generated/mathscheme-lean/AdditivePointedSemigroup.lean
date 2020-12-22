import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AdditivePointedSemigroup   
  structure AdditivePointedSemigroup  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z)))) 
  
  open AdditivePointedSemigroup
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AdditivePointedSemigroup A1)) (Ad2 : (AdditivePointedSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ad1)) = (zero Ad2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AdditivePointedSemigroup A1)) (Ad2 : (AdditivePointedSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ad1) (zero Ad2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2)))))) 
  
  inductive AdditivePointedSemigroupTerm   : Type  
     | zeroL : AdditivePointedSemigroupTerm 
     | plusL : (AdditivePointedSemigroupTerm → (AdditivePointedSemigroupTerm → AdditivePointedSemigroupTerm))  
      open AdditivePointedSemigroupTerm 
  
  inductive ClAdditivePointedSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClAdditivePointedSemigroupTerm) 
     | zeroCl : ClAdditivePointedSemigroupTerm 
     | plusCl : (ClAdditivePointedSemigroupTerm → (ClAdditivePointedSemigroupTerm → ClAdditivePointedSemigroupTerm))  
      open ClAdditivePointedSemigroupTerm 
  
  inductive OpAdditivePointedSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAdditivePointedSemigroupTerm) 
     | zeroOL : OpAdditivePointedSemigroupTerm 
     | plusOL : (OpAdditivePointedSemigroupTerm → (OpAdditivePointedSemigroupTerm → OpAdditivePointedSemigroupTerm))  
      open OpAdditivePointedSemigroupTerm 
  
  inductive OpAdditivePointedSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAdditivePointedSemigroupTerm2) 
     | sing2 : (A → OpAdditivePointedSemigroupTerm2) 
     | zeroOL2 : OpAdditivePointedSemigroupTerm2 
     | plusOL2 : (OpAdditivePointedSemigroupTerm2 → (OpAdditivePointedSemigroupTerm2 → OpAdditivePointedSemigroupTerm2))  
      open OpAdditivePointedSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAdditivePointedSemigroupTerm A) → (ClAdditivePointedSemigroupTerm A)) 
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAdditivePointedSemigroupTerm n) → (OpAdditivePointedSemigroupTerm n)) 
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAdditivePointedSemigroupTerm2 n A) → (OpAdditivePointedSemigroupTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AdditivePointedSemigroup A) → (AdditivePointedSemigroupTerm → A)) 
  | Ad zeroL := (zero Ad)  
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  def evalCl   {A : Type}  : ((AdditivePointedSemigroup A) → ((ClAdditivePointedSemigroupTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad zeroCl := (zero Ad)  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AdditivePointedSemigroup A) → ((vector A n) → ((OpAdditivePointedSemigroupTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars zeroOL := (zero Ad)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((AdditivePointedSemigroup A) → ((vector A n) → ((OpAdditivePointedSemigroupTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars zeroOL2 := (zero Ad)  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  def inductionB   (P : (AdditivePointedSemigroupTerm → Type))  : ((P zeroL) → ((∀ (x1 x2 : AdditivePointedSemigroupTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : AdditivePointedSemigroupTerm) , (P x)))) 
  | p0l pplusl zeroL := p0l  
  | p0l pplusl (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl x1) (inductionB p0l pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClAdditivePointedSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClAdditivePointedSemigroupTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClAdditivePointedSemigroupTerm A)) , (P x))))) 
  | psing p0cl ppluscl (sing x1) := (psing x1)  
  | psing p0cl ppluscl zeroCl := p0cl  
  | psing p0cl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl x1) (inductionCl psing p0cl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAdditivePointedSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpAdditivePointedSemigroupTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpAdditivePointedSemigroupTerm n)) , (P x))))) 
  | pv p0ol pplusol (v x1) := (pv x1)  
  | pv p0ol pplusol zeroOL := p0ol  
  | pv p0ol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol x1) (inductionOpB pv p0ol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAdditivePointedSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpAdditivePointedSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpAdditivePointedSemigroupTerm2 n A)) , (P x)))))) 
  | pv2 psing2 p0ol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 x2))  
  def stageB  : (AdditivePointedSemigroupTerm → (Staged AdditivePointedSemigroupTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAdditivePointedSemigroupTerm A) → (Staged (ClAdditivePointedSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAdditivePointedSemigroupTerm n) → (Staged (OpAdditivePointedSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAdditivePointedSemigroupTerm2 n A) → (Staged (OpAdditivePointedSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AdditivePointedSemigroup