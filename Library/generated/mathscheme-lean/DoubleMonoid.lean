import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section DoubleMonoid   
  structure DoubleMonoid  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (one : A)
       (times : (A → (A → A)))
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z)))) 
  
  open DoubleMonoid
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS)))
       (oneS : AS)
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Do1 : (DoubleMonoid A1)) (Do2 : (DoubleMonoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Do1)) = (zero Do2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Do1) x1 x2)) = ((plus Do2) (hom x1) (hom x2))))
       (pres_one : (hom (one Do1)) = (one Do2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Do1) x1 x2)) = ((times Do2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Do1 : (DoubleMonoid A1)) (Do2 : (DoubleMonoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Do1) (zero Do2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Do1) x1 x2) ((plus Do2) y1 y2))))))
       (interp_one : (interp (one Do1) (one Do2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Do1) x1 x2) ((times Do2) y1 y2)))))) 
  
  inductive DoubleMonoidTerm   : Type  
     | zeroL : DoubleMonoidTerm 
     | plusL : (DoubleMonoidTerm → (DoubleMonoidTerm → DoubleMonoidTerm)) 
     | oneL : DoubleMonoidTerm 
     | timesL : (DoubleMonoidTerm → (DoubleMonoidTerm → DoubleMonoidTerm))  
      open DoubleMonoidTerm 
  
  inductive ClDoubleMonoidTerm  (A : Type) : Type  
     | sing : (A → ClDoubleMonoidTerm) 
     | zeroCl : ClDoubleMonoidTerm 
     | plusCl : (ClDoubleMonoidTerm → (ClDoubleMonoidTerm → ClDoubleMonoidTerm)) 
     | oneCl : ClDoubleMonoidTerm 
     | timesCl : (ClDoubleMonoidTerm → (ClDoubleMonoidTerm → ClDoubleMonoidTerm))  
      open ClDoubleMonoidTerm 
  
  inductive OpDoubleMonoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpDoubleMonoidTerm) 
     | zeroOL : OpDoubleMonoidTerm 
     | plusOL : (OpDoubleMonoidTerm → (OpDoubleMonoidTerm → OpDoubleMonoidTerm)) 
     | oneOL : OpDoubleMonoidTerm 
     | timesOL : (OpDoubleMonoidTerm → (OpDoubleMonoidTerm → OpDoubleMonoidTerm))  
      open OpDoubleMonoidTerm 
  
  inductive OpDoubleMonoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpDoubleMonoidTerm2) 
     | sing2 : (A → OpDoubleMonoidTerm2) 
     | zeroOL2 : OpDoubleMonoidTerm2 
     | plusOL2 : (OpDoubleMonoidTerm2 → (OpDoubleMonoidTerm2 → OpDoubleMonoidTerm2)) 
     | oneOL2 : OpDoubleMonoidTerm2 
     | timesOL2 : (OpDoubleMonoidTerm2 → (OpDoubleMonoidTerm2 → OpDoubleMonoidTerm2))  
      open OpDoubleMonoidTerm2 
  
  def simplifyCl   (A : Type)  : ((ClDoubleMonoidTerm A) → (ClDoubleMonoidTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpDoubleMonoidTerm n) → (OpDoubleMonoidTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpDoubleMonoidTerm2 n A) → (OpDoubleMonoidTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((DoubleMonoid A) → (DoubleMonoidTerm → A)) 
  | Do zeroL := (zero Do)  
  | Do (plusL x1 x2) := ((plus Do) (evalB Do x1) (evalB Do x2))  
  | Do oneL := (one Do)  
  | Do (timesL x1 x2) := ((times Do) (evalB Do x1) (evalB Do x2))  
  def evalCl   {A : Type}  : ((DoubleMonoid A) → ((ClDoubleMonoidTerm A) → A)) 
  | Do (sing x1) := x1  
  | Do zeroCl := (zero Do)  
  | Do (plusCl x1 x2) := ((plus Do) (evalCl Do x1) (evalCl Do x2))  
  | Do oneCl := (one Do)  
  | Do (timesCl x1 x2) := ((times Do) (evalCl Do x1) (evalCl Do x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((DoubleMonoid A) → ((vector A n) → ((OpDoubleMonoidTerm n) → A))) 
  | Do vars (v x1) := (nth vars x1)  
  | Do vars zeroOL := (zero Do)  
  | Do vars (plusOL x1 x2) := ((plus Do) (evalOpB Do vars x1) (evalOpB Do vars x2))  
  | Do vars oneOL := (one Do)  
  | Do vars (timesOL x1 x2) := ((times Do) (evalOpB Do vars x1) (evalOpB Do vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((DoubleMonoid A) → ((vector A n) → ((OpDoubleMonoidTerm2 n A) → A))) 
  | Do vars (v2 x1) := (nth vars x1)  
  | Do vars (sing2 x1) := x1  
  | Do vars zeroOL2 := (zero Do)  
  | Do vars (plusOL2 x1 x2) := ((plus Do) (evalOp Do vars x1) (evalOp Do vars x2))  
  | Do vars oneOL2 := (one Do)  
  | Do vars (timesOL2 x1 x2) := ((times Do) (evalOp Do vars x1) (evalOp Do vars x2))  
  def inductionB   (P : (DoubleMonoidTerm → Type))  : ((P zeroL) → ((∀ (x1 x2 : DoubleMonoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P oneL) → ((∀ (x1 x2 : DoubleMonoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : DoubleMonoidTerm) , (P x)))))) 
  | p0l pplusl p1l ptimesl zeroL := p0l  
  | p0l pplusl p1l ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl p1l ptimesl x1) (inductionB p0l pplusl p1l ptimesl x2))  
  | p0l pplusl p1l ptimesl oneL := p1l  
  | p0l pplusl p1l ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l pplusl p1l ptimesl x1) (inductionB p0l pplusl p1l ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClDoubleMonoidTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClDoubleMonoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P oneCl) → ((∀ (x1 x2 : (ClDoubleMonoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClDoubleMonoidTerm A)) , (P x))))))) 
  | psing p0cl ppluscl p1cl ptimescl (sing x1) := (psing x1)  
  | psing p0cl ppluscl p1cl ptimescl zeroCl := p0cl  
  | psing p0cl ppluscl p1cl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl p1cl ptimescl x1) (inductionCl psing p0cl ppluscl p1cl ptimescl x2))  
  | psing p0cl ppluscl p1cl ptimescl oneCl := p1cl  
  | psing p0cl ppluscl p1cl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ppluscl p1cl ptimescl x1) (inductionCl psing p0cl ppluscl p1cl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpDoubleMonoidTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpDoubleMonoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P oneOL) → ((∀ (x1 x2 : (OpDoubleMonoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpDoubleMonoidTerm n)) , (P x))))))) 
  | pv p0ol pplusol p1ol ptimesol (v x1) := (pv x1)  
  | pv p0ol pplusol p1ol ptimesol zeroOL := p0ol  
  | pv p0ol pplusol p1ol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol p1ol ptimesol x1) (inductionOpB pv p0ol pplusol p1ol ptimesol x2))  
  | pv p0ol pplusol p1ol ptimesol oneOL := p1ol  
  | pv p0ol pplusol p1ol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol pplusol p1ol ptimesol x1) (inductionOpB pv p0ol pplusol p1ol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpDoubleMonoidTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpDoubleMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 x2 : (OpDoubleMonoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpDoubleMonoidTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 oneOL2 := p1ol2  
  | pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 p1ol2 ptimesol2 x2))  
  def stageB  : (DoubleMonoidTerm → (Staged DoubleMonoidTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClDoubleMonoidTerm A) → (Staged (ClDoubleMonoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpDoubleMonoidTerm n) → (Staged (OpDoubleMonoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpDoubleMonoidTerm2 n A) → (Staged (OpDoubleMonoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end DoubleMonoid