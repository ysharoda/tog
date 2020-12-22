import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AdditiveCommutativeMonoid   
  structure AdditiveCommutativeMonoid  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x))) 
  
  open AdditiveCommutativeMonoid
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveCommutativeMonoid A1)) (Ad2 : (AdditiveCommutativeMonoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ad1)) = (zero Ad2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveCommutativeMonoid A1)) (Ad2 : (AdditiveCommutativeMonoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2))))))
       (interp_zero : (interp (zero Ad1) (zero Ad2))) 
  
  inductive AdditiveCommutativeMonoidTerm   : Type  
     | plusL : (AdditiveCommutativeMonoidTerm → (AdditiveCommutativeMonoidTerm → AdditiveCommutativeMonoidTerm)) 
     | zeroL : AdditiveCommutativeMonoidTerm  
      open AdditiveCommutativeMonoidTerm 
  
  inductive ClAdditiveCommutativeMonoidTerm  (A : Type) : Type  
     | sing : (A → ClAdditiveCommutativeMonoidTerm) 
     | plusCl : (ClAdditiveCommutativeMonoidTerm → (ClAdditiveCommutativeMonoidTerm → ClAdditiveCommutativeMonoidTerm)) 
     | zeroCl : ClAdditiveCommutativeMonoidTerm  
      open ClAdditiveCommutativeMonoidTerm 
  
  inductive OpAdditiveCommutativeMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAdditiveCommutativeMonoidTerm) 
     | plusOL : (OpAdditiveCommutativeMonoidTerm → (OpAdditiveCommutativeMonoidTerm → OpAdditiveCommutativeMonoidTerm)) 
     | zeroOL : OpAdditiveCommutativeMonoidTerm  
      open OpAdditiveCommutativeMonoidTerm 
  
  inductive OpAdditiveCommutativeMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAdditiveCommutativeMonoidTerm2) 
     | sing2 : (A → OpAdditiveCommutativeMonoidTerm2) 
     | plusOL2 : (OpAdditiveCommutativeMonoidTerm2 → (OpAdditiveCommutativeMonoidTerm2 → OpAdditiveCommutativeMonoidTerm2)) 
     | zeroOL2 : OpAdditiveCommutativeMonoidTerm2  
      open OpAdditiveCommutativeMonoidTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAdditiveCommutativeMonoidTerm A) → (ClAdditiveCommutativeMonoidTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAdditiveCommutativeMonoidTerm n) → (OpAdditiveCommutativeMonoidTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAdditiveCommutativeMonoidTerm2 n A) → (OpAdditiveCommutativeMonoidTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AdditiveCommutativeMonoid A) → (AdditiveCommutativeMonoidTerm → A)) 
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  | Ad zeroL := (zero Ad)  
  def evalCl   {A : Type}  : ((AdditiveCommutativeMonoid A) → ((ClAdditiveCommutativeMonoidTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  | Ad zeroCl := (zero Ad)  
  def evalOpB   {A : Type} (n : ℕ)  : ((AdditiveCommutativeMonoid A) → ((vector A n) → ((OpAdditiveCommutativeMonoidTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  | Ad vars zeroOL := (zero Ad)  
  def evalOp   {A : Type} (n : ℕ)  : ((AdditiveCommutativeMonoid A) → ((vector A n) → ((OpAdditiveCommutativeMonoidTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  | Ad vars zeroOL2 := (zero Ad)  
  def inductionB   (P : (AdditiveCommutativeMonoidTerm → Type))  : ((∀ (x1 x2 : AdditiveCommutativeMonoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → (∀ (x : AdditiveCommutativeMonoidTerm) , (P x)))) 
  | pplusl p0l (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l x1) (inductionB pplusl p0l x2))  
  | pplusl p0l zeroL := p0l  
  def inductionCl   (A : Type) (P : ((ClAdditiveCommutativeMonoidTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAdditiveCommutativeMonoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → (∀ (x : (ClAdditiveCommutativeMonoidTerm A)) , (P x))))) 
  | psing ppluscl p0cl (sing x1) := (psing x1)  
  | psing ppluscl p0cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl x1) (inductionCl psing ppluscl p0cl x2))  
  | psing ppluscl p0cl zeroCl := p0cl  
  def inductionOpB   (n : ℕ) (P : ((OpAdditiveCommutativeMonoidTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAdditiveCommutativeMonoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → (∀ (x : (OpAdditiveCommutativeMonoidTerm n)) , (P x))))) 
  | pv pplusol p0ol (v x1) := (pv x1)  
  | pv pplusol p0ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol x1) (inductionOpB pv pplusol p0ol x2))  
  | pv pplusol p0ol zeroOL := p0ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAdditiveCommutativeMonoidTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAdditiveCommutativeMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → (∀ (x : (OpAdditiveCommutativeMonoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 p0ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 zeroOL2 := p0ol2  
  def stageB  : (AdditiveCommutativeMonoidTerm → (Staged AdditiveCommutativeMonoidTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  def stageCl   (A : Type)  : ((ClAdditiveCommutativeMonoidTerm A) → (Staged (ClAdditiveCommutativeMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  def stageOpB   (n : ℕ)  : ((OpAdditiveCommutativeMonoidTerm n) → (Staged (OpAdditiveCommutativeMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAdditiveCommutativeMonoidTerm2 n A) → (Staged (OpAdditiveCommutativeMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A)) 
  
end AdditiveCommutativeMonoid