import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AdditiveCommutativeSemigroup   
  structure AdditiveCommutativeSemigroup  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z)))) 
  
  open AdditiveCommutativeSemigroup
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveCommutativeSemigroup A1)) (Ad2 : (AdditiveCommutativeSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveCommutativeSemigroup A1)) (Ad2 : (AdditiveCommutativeSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2)))))) 
  
  inductive AdditiveCommutativeSemigroupTerm   : Type  
     | plusL : (AdditiveCommutativeSemigroupTerm → (AdditiveCommutativeSemigroupTerm → AdditiveCommutativeSemigroupTerm))  
      open AdditiveCommutativeSemigroupTerm 
  
  inductive ClAdditiveCommutativeSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClAdditiveCommutativeSemigroupTerm) 
     | plusCl : (ClAdditiveCommutativeSemigroupTerm → (ClAdditiveCommutativeSemigroupTerm → ClAdditiveCommutativeSemigroupTerm))  
      open ClAdditiveCommutativeSemigroupTerm 
  
  inductive OpAdditiveCommutativeSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAdditiveCommutativeSemigroupTerm) 
     | plusOL : (OpAdditiveCommutativeSemigroupTerm → (OpAdditiveCommutativeSemigroupTerm → OpAdditiveCommutativeSemigroupTerm))  
      open OpAdditiveCommutativeSemigroupTerm 
  
  inductive OpAdditiveCommutativeSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAdditiveCommutativeSemigroupTerm2) 
     | sing2 : (A → OpAdditiveCommutativeSemigroupTerm2) 
     | plusOL2 : (OpAdditiveCommutativeSemigroupTerm2 → (OpAdditiveCommutativeSemigroupTerm2 → OpAdditiveCommutativeSemigroupTerm2))  
      open OpAdditiveCommutativeSemigroupTerm2 
  
  def simplifyCl   {A : Type}  : ((ClAdditiveCommutativeSemigroupTerm A) → (ClAdditiveCommutativeSemigroupTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpAdditiveCommutativeSemigroupTerm n) → (OpAdditiveCommutativeSemigroupTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpAdditiveCommutativeSemigroupTerm2 n A) → (OpAdditiveCommutativeSemigroupTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AdditiveCommutativeSemigroup A) → (AdditiveCommutativeSemigroupTerm → A)) 
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  def evalCl   {A : Type}  : ((AdditiveCommutativeSemigroup A) → ((ClAdditiveCommutativeSemigroupTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((AdditiveCommutativeSemigroup A) → ((vector A n) → ((OpAdditiveCommutativeSemigroupTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((AdditiveCommutativeSemigroup A) → ((vector A n) → ((OpAdditiveCommutativeSemigroupTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  def inductionB   {P : (AdditiveCommutativeSemigroupTerm → Type)}  : ((∀ (x1 x2 : AdditiveCommutativeSemigroupTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : AdditiveCommutativeSemigroupTerm) , (P x))) 
  | pplusl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl x1) (inductionB pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClAdditiveCommutativeSemigroupTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAdditiveCommutativeSemigroupTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClAdditiveCommutativeSemigroupTerm A)) , (P x)))) 
  | psing ppluscl (sing x1) := (psing x1)  
  | psing ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl x1) (inductionCl psing ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpAdditiveCommutativeSemigroupTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAdditiveCommutativeSemigroupTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpAdditiveCommutativeSemigroupTerm n)) , (P x)))) 
  | pv pplusol (v x1) := (pv x1)  
  | pv pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol x1) (inductionOpB pv pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpAdditiveCommutativeSemigroupTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAdditiveCommutativeSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpAdditiveCommutativeSemigroupTerm2 n A)) , (P x))))) 
  | pv2 psing2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 x1) (inductionOp pv2 psing2 pplusol2 x2))  
  def stageB  : (AdditiveCommutativeSemigroupTerm → (Staged AdditiveCommutativeSemigroupTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClAdditiveCommutativeSemigroupTerm A) → (Staged (ClAdditiveCommutativeSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpAdditiveCommutativeSemigroupTerm n) → (Staged (OpAdditiveCommutativeSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpAdditiveCommutativeSemigroupTerm2 n A) → (Staged (OpAdditiveCommutativeSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AdditiveCommutativeSemigroup