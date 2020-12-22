import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AddCommMonWithMultSemigroup   
  structure AddCommMonWithMultSemigroup  (A : Type) : Type := 
       (times : (A → (A → A)))
       (zero : A)
       (plus : (A → (A → A)))
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z)))) 
  
  open AddCommMonWithMultSemigroup
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (zeroS : AS)
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AddCommMonWithMultSemigroup A1)) (Ad2 : (AddCommMonWithMultSemigroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ad1) x1 x2)) = ((times Ad2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ad1)) = (zero Ad2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AddCommMonWithMultSemigroup A1)) (Ad2 : (AddCommMonWithMultSemigroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ad1) x1 x2) ((times Ad2) y1 y2))))))
       (interp_zero : (interp (zero Ad1) (zero Ad2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2)))))) 
  
  inductive AddCommMonWithMultSemigroupTerm   : Type  
     | timesL : (AddCommMonWithMultSemigroupTerm → (AddCommMonWithMultSemigroupTerm → AddCommMonWithMultSemigroupTerm)) 
     | zeroL : AddCommMonWithMultSemigroupTerm 
     | plusL : (AddCommMonWithMultSemigroupTerm → (AddCommMonWithMultSemigroupTerm → AddCommMonWithMultSemigroupTerm))  
      open AddCommMonWithMultSemigroupTerm 
  
  inductive ClAddCommMonWithMultSemigroupTerm  (A : Type) : Type  
     | sing : (A → ClAddCommMonWithMultSemigroupTerm) 
     | timesCl : (ClAddCommMonWithMultSemigroupTerm → (ClAddCommMonWithMultSemigroupTerm → ClAddCommMonWithMultSemigroupTerm)) 
     | zeroCl : ClAddCommMonWithMultSemigroupTerm 
     | plusCl : (ClAddCommMonWithMultSemigroupTerm → (ClAddCommMonWithMultSemigroupTerm → ClAddCommMonWithMultSemigroupTerm))  
      open ClAddCommMonWithMultSemigroupTerm 
  
  inductive OpAddCommMonWithMultSemigroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAddCommMonWithMultSemigroupTerm) 
     | timesOL : (OpAddCommMonWithMultSemigroupTerm → (OpAddCommMonWithMultSemigroupTerm → OpAddCommMonWithMultSemigroupTerm)) 
     | zeroOL : OpAddCommMonWithMultSemigroupTerm 
     | plusOL : (OpAddCommMonWithMultSemigroupTerm → (OpAddCommMonWithMultSemigroupTerm → OpAddCommMonWithMultSemigroupTerm))  
      open OpAddCommMonWithMultSemigroupTerm 
  
  inductive OpAddCommMonWithMultSemigroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAddCommMonWithMultSemigroupTerm2) 
     | sing2 : (A → OpAddCommMonWithMultSemigroupTerm2) 
     | timesOL2 : (OpAddCommMonWithMultSemigroupTerm2 → (OpAddCommMonWithMultSemigroupTerm2 → OpAddCommMonWithMultSemigroupTerm2)) 
     | zeroOL2 : OpAddCommMonWithMultSemigroupTerm2 
     | plusOL2 : (OpAddCommMonWithMultSemigroupTerm2 → (OpAddCommMonWithMultSemigroupTerm2 → OpAddCommMonWithMultSemigroupTerm2))  
      open OpAddCommMonWithMultSemigroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAddCommMonWithMultSemigroupTerm A) → (ClAddCommMonWithMultSemigroupTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAddCommMonWithMultSemigroupTerm n) → (OpAddCommMonWithMultSemigroupTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAddCommMonWithMultSemigroupTerm2 n A) → (OpAddCommMonWithMultSemigroupTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AddCommMonWithMultSemigroup A) → (AddCommMonWithMultSemigroupTerm → A)) 
  | Ad (timesL x1 x2) := ((times Ad) (evalB Ad x1) (evalB Ad x2))  
  | Ad zeroL := (zero Ad)  
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  def evalCl   {A : Type}  : ((AddCommMonWithMultSemigroup A) → ((ClAddCommMonWithMultSemigroupTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad (timesCl x1 x2) := ((times Ad) (evalCl Ad x1) (evalCl Ad x2))  
  | Ad zeroCl := (zero Ad)  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AddCommMonWithMultSemigroup A) → ((vector A n) → ((OpAddCommMonWithMultSemigroupTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars (timesOL x1 x2) := ((times Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  | Ad vars zeroOL := (zero Ad)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((AddCommMonWithMultSemigroup A) → ((vector A n) → ((OpAddCommMonWithMultSemigroupTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars (timesOL2 x1 x2) := ((times Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  | Ad vars zeroOL2 := (zero Ad)  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  def inductionB   (P : (AddCommMonWithMultSemigroupTerm → Type))  : ((∀ (x1 x2 : AddCommMonWithMultSemigroupTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P zeroL) → ((∀ (x1 x2 : AddCommMonWithMultSemigroupTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : AddCommMonWithMultSemigroupTerm) , (P x))))) 
  | ptimesl p0l pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p0l pplusl x1) (inductionB ptimesl p0l pplusl x2))  
  | ptimesl p0l pplusl zeroL := p0l  
  | ptimesl p0l pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl p0l pplusl x1) (inductionB ptimesl p0l pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClAddCommMonWithMultSemigroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAddCommMonWithMultSemigroupTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 x2 : (ClAddCommMonWithMultSemigroupTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClAddCommMonWithMultSemigroupTerm A)) , (P x)))))) 
  | psing ptimescl p0cl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl p0cl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p0cl ppluscl x1) (inductionCl psing ptimescl p0cl ppluscl x2))  
  | psing ptimescl p0cl ppluscl zeroCl := p0cl  
  | psing ptimescl p0cl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl p0cl ppluscl x1) (inductionCl psing ptimescl p0cl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAddCommMonWithMultSemigroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAddCommMonWithMultSemigroupTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 x2 : (OpAddCommMonWithMultSemigroupTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpAddCommMonWithMultSemigroupTerm n)) , (P x)))))) 
  | pv ptimesol p0ol pplusol (v x1) := (pv x1)  
  | pv ptimesol p0ol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p0ol pplusol x1) (inductionOpB pv ptimesol p0ol pplusol x2))  
  | pv ptimesol p0ol pplusol zeroOL := p0ol  
  | pv ptimesol p0ol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol p0ol pplusol x1) (inductionOpB pv ptimesol p0ol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAddCommMonWithMultSemigroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAddCommMonWithMultSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpAddCommMonWithMultSemigroupTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpAddCommMonWithMultSemigroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 ptimesol2 p0ol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p0ol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p0ol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p0ol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p0ol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 p0ol2 pplusol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 p0ol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 p0ol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 p0ol2 pplusol2 x2))  
  def stageB  : (AddCommMonWithMultSemigroupTerm → (Staged AddCommMonWithMultSemigroupTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAddCommMonWithMultSemigroupTerm A) → (Staged (ClAddCommMonWithMultSemigroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAddCommMonWithMultSemigroupTerm n) → (Staged (OpAddCommMonWithMultSemigroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAddCommMonWithMultSemigroupTerm2 n A) → (Staged (OpAddCommMonWithMultSemigroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AddCommMonWithMultSemigroup