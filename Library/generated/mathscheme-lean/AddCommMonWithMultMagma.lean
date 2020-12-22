import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AddCommMonWithMultMagma   
  structure AddCommMonWithMultMagma  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (times : (A → (A → A))) 
  
  open AddCommMonWithMultMagma
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AddCommMonWithMultMagma A1)) (Ad2 : (AddCommMonWithMultMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ad1)) = (zero Ad2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ad1) x1 x2)) = ((times Ad2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AddCommMonWithMultMagma A1)) (Ad2 : (AddCommMonWithMultMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ad1) (zero Ad2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ad1) x1 x2) ((times Ad2) y1 y2)))))) 
  
  inductive AddCommMonWithMultMagmaTerm   : Type  
     | zeroL : AddCommMonWithMultMagmaTerm 
     | plusL : (AddCommMonWithMultMagmaTerm → (AddCommMonWithMultMagmaTerm → AddCommMonWithMultMagmaTerm)) 
     | timesL : (AddCommMonWithMultMagmaTerm → (AddCommMonWithMultMagmaTerm → AddCommMonWithMultMagmaTerm))  
      open AddCommMonWithMultMagmaTerm 
  
  inductive ClAddCommMonWithMultMagmaTerm  (A : Type) : Type  
     | sing : (A → ClAddCommMonWithMultMagmaTerm) 
     | zeroCl : ClAddCommMonWithMultMagmaTerm 
     | plusCl : (ClAddCommMonWithMultMagmaTerm → (ClAddCommMonWithMultMagmaTerm → ClAddCommMonWithMultMagmaTerm)) 
     | timesCl : (ClAddCommMonWithMultMagmaTerm → (ClAddCommMonWithMultMagmaTerm → ClAddCommMonWithMultMagmaTerm))  
      open ClAddCommMonWithMultMagmaTerm 
  
  inductive OpAddCommMonWithMultMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAddCommMonWithMultMagmaTerm) 
     | zeroOL : OpAddCommMonWithMultMagmaTerm 
     | plusOL : (OpAddCommMonWithMultMagmaTerm → (OpAddCommMonWithMultMagmaTerm → OpAddCommMonWithMultMagmaTerm)) 
     | timesOL : (OpAddCommMonWithMultMagmaTerm → (OpAddCommMonWithMultMagmaTerm → OpAddCommMonWithMultMagmaTerm))  
      open OpAddCommMonWithMultMagmaTerm 
  
  inductive OpAddCommMonWithMultMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAddCommMonWithMultMagmaTerm2) 
     | sing2 : (A → OpAddCommMonWithMultMagmaTerm2) 
     | zeroOL2 : OpAddCommMonWithMultMagmaTerm2 
     | plusOL2 : (OpAddCommMonWithMultMagmaTerm2 → (OpAddCommMonWithMultMagmaTerm2 → OpAddCommMonWithMultMagmaTerm2)) 
     | timesOL2 : (OpAddCommMonWithMultMagmaTerm2 → (OpAddCommMonWithMultMagmaTerm2 → OpAddCommMonWithMultMagmaTerm2))  
      open OpAddCommMonWithMultMagmaTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAddCommMonWithMultMagmaTerm A) → (ClAddCommMonWithMultMagmaTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAddCommMonWithMultMagmaTerm n) → (OpAddCommMonWithMultMagmaTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAddCommMonWithMultMagmaTerm2 n A) → (OpAddCommMonWithMultMagmaTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AddCommMonWithMultMagma A) → (AddCommMonWithMultMagmaTerm → A)) 
  | Ad zeroL := (zero Ad)  
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  | Ad (timesL x1 x2) := ((times Ad) (evalB Ad x1) (evalB Ad x2))  
  def evalCl   {A : Type}  : ((AddCommMonWithMultMagma A) → ((ClAddCommMonWithMultMagmaTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad zeroCl := (zero Ad)  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  | Ad (timesCl x1 x2) := ((times Ad) (evalCl Ad x1) (evalCl Ad x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AddCommMonWithMultMagma A) → ((vector A n) → ((OpAddCommMonWithMultMagmaTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars zeroOL := (zero Ad)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  | Ad vars (timesOL x1 x2) := ((times Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((AddCommMonWithMultMagma A) → ((vector A n) → ((OpAddCommMonWithMultMagmaTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars zeroOL2 := (zero Ad)  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  | Ad vars (timesOL2 x1 x2) := ((times Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  def inductionB   (P : (AddCommMonWithMultMagmaTerm → Type))  : ((P zeroL) → ((∀ (x1 x2 : AddCommMonWithMultMagmaTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : AddCommMonWithMultMagmaTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : AddCommMonWithMultMagmaTerm) , (P x))))) 
  | p0l pplusl ptimesl zeroL := p0l  
  | p0l pplusl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl ptimesl x1) (inductionB p0l pplusl ptimesl x2))  
  | p0l pplusl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l pplusl ptimesl x1) (inductionB p0l pplusl ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClAddCommMonWithMultMagmaTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClAddCommMonWithMultMagmaTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClAddCommMonWithMultMagmaTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClAddCommMonWithMultMagmaTerm A)) , (P x)))))) 
  | psing p0cl ppluscl ptimescl (sing x1) := (psing x1)  
  | psing p0cl ppluscl ptimescl zeroCl := p0cl  
  | psing p0cl ppluscl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl ptimescl x1) (inductionCl psing p0cl ppluscl ptimescl x2))  
  | psing p0cl ppluscl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ppluscl ptimescl x1) (inductionCl psing p0cl ppluscl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAddCommMonWithMultMagmaTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpAddCommMonWithMultMagmaTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpAddCommMonWithMultMagmaTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpAddCommMonWithMultMagmaTerm n)) , (P x)))))) 
  | pv p0ol pplusol ptimesol (v x1) := (pv x1)  
  | pv p0ol pplusol ptimesol zeroOL := p0ol  
  | pv p0ol pplusol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol ptimesol x1) (inductionOpB pv p0ol pplusol ptimesol x2))  
  | pv p0ol pplusol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol pplusol ptimesol x1) (inductionOpB pv p0ol pplusol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAddCommMonWithMultMagmaTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpAddCommMonWithMultMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpAddCommMonWithMultMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpAddCommMonWithMultMagmaTerm2 n A)) , (P x))))))) 
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x2))  
  def stageB  : (AddCommMonWithMultMagmaTerm → (Staged AddCommMonWithMultMagmaTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAddCommMonWithMultMagmaTerm A) → (Staged (ClAddCommMonWithMultMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAddCommMonWithMultMagmaTerm n) → (Staged (OpAddCommMonWithMultMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAddCommMonWithMultMagmaTerm2 n A) → (Staged (OpAddCommMonWithMultMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AddCommMonWithMultMagma