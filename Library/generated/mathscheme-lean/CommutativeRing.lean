import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section CommutativeRing   
  structure CommutativeRing  (A : Type) : Type := 
       (one : A)
       (times : (A → (A → A)))
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero)) 
  
  open CommutativeRing
  structure Sig  (AS : Type) : Type := 
       (oneS : AS)
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (oneP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Co1 : (CommutativeRing A1)) (Co2 : (CommutativeRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_one : (hom (one Co1)) = (one Co2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Co1) x1 x2)) = ((times Co2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Co1) x1 x2)) = ((plus Co2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Co1)) = (zero Co2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Co1) x1)) = ((neg Co2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Co1 : (CommutativeRing A1)) (Co2 : (CommutativeRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_one : (interp (one Co1) (one Co2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Co1) x1 x2) ((times Co2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Co1) x1 x2) ((plus Co2) y1 y2))))))
       (interp_zero : (interp (zero Co1) (zero Co2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Co1) x1) ((neg Co2) y1))))) 
  
  inductive CommutativeRingTerm   : Type  
     | oneL : CommutativeRingTerm 
     | timesL : (CommutativeRingTerm → (CommutativeRingTerm → CommutativeRingTerm)) 
     | plusL : (CommutativeRingTerm → (CommutativeRingTerm → CommutativeRingTerm)) 
     | zeroL : CommutativeRingTerm 
     | negL : (CommutativeRingTerm → CommutativeRingTerm)  
      open CommutativeRingTerm 
  
  inductive ClCommutativeRingTerm  (A : Type) : Type  
     | sing : (A → ClCommutativeRingTerm) 
     | oneCl : ClCommutativeRingTerm 
     | timesCl : (ClCommutativeRingTerm → (ClCommutativeRingTerm → ClCommutativeRingTerm)) 
     | plusCl : (ClCommutativeRingTerm → (ClCommutativeRingTerm → ClCommutativeRingTerm)) 
     | zeroCl : ClCommutativeRingTerm 
     | negCl : (ClCommutativeRingTerm → ClCommutativeRingTerm)  
      open ClCommutativeRingTerm 
  
  inductive OpCommutativeRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCommutativeRingTerm) 
     | oneOL : OpCommutativeRingTerm 
     | timesOL : (OpCommutativeRingTerm → (OpCommutativeRingTerm → OpCommutativeRingTerm)) 
     | plusOL : (OpCommutativeRingTerm → (OpCommutativeRingTerm → OpCommutativeRingTerm)) 
     | zeroOL : OpCommutativeRingTerm 
     | negOL : (OpCommutativeRingTerm → OpCommutativeRingTerm)  
      open OpCommutativeRingTerm 
  
  inductive OpCommutativeRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCommutativeRingTerm2) 
     | sing2 : (A → OpCommutativeRingTerm2) 
     | oneOL2 : OpCommutativeRingTerm2 
     | timesOL2 : (OpCommutativeRingTerm2 → (OpCommutativeRingTerm2 → OpCommutativeRingTerm2)) 
     | plusOL2 : (OpCommutativeRingTerm2 → (OpCommutativeRingTerm2 → OpCommutativeRingTerm2)) 
     | zeroOL2 : OpCommutativeRingTerm2 
     | negOL2 : (OpCommutativeRingTerm2 → OpCommutativeRingTerm2)  
      open OpCommutativeRingTerm2 
  
  def simplifyCl   {A : Type}  : ((ClCommutativeRingTerm A) → (ClCommutativeRingTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | oneCl := oneCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpCommutativeRingTerm n) → (OpCommutativeRingTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | oneOL := oneOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpCommutativeRingTerm2 n A) → (OpCommutativeRingTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | oneOL2 := oneOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((CommutativeRing A) → (CommutativeRingTerm → A)) 
  | Co oneL := (one Co)  
  | Co (timesL x1 x2) := ((times Co) (evalB Co x1) (evalB Co x2))  
  | Co (plusL x1 x2) := ((plus Co) (evalB Co x1) (evalB Co x2))  
  | Co zeroL := (zero Co)  
  | Co (negL x1) := ((neg Co) (evalB Co x1))  
  def evalCl   {A : Type}  : ((CommutativeRing A) → ((ClCommutativeRingTerm A) → A)) 
  | Co (sing x1) := x1  
  | Co oneCl := (one Co)  
  | Co (timesCl x1 x2) := ((times Co) (evalCl Co x1) (evalCl Co x2))  
  | Co (plusCl x1 x2) := ((plus Co) (evalCl Co x1) (evalCl Co x2))  
  | Co zeroCl := (zero Co)  
  | Co (negCl x1) := ((neg Co) (evalCl Co x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((CommutativeRing A) → ((vector A n) → ((OpCommutativeRingTerm n) → A))) 
  | Co vars (v x1) := (nth vars x1)  
  | Co vars oneOL := (one Co)  
  | Co vars (timesOL x1 x2) := ((times Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  | Co vars (plusOL x1 x2) := ((plus Co) (evalOpB Co vars x1) (evalOpB Co vars x2))  
  | Co vars zeroOL := (zero Co)  
  | Co vars (negOL x1) := ((neg Co) (evalOpB Co vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((CommutativeRing A) → ((vector A n) → ((OpCommutativeRingTerm2 n A) → A))) 
  | Co vars (v2 x1) := (nth vars x1)  
  | Co vars (sing2 x1) := x1  
  | Co vars oneOL2 := (one Co)  
  | Co vars (timesOL2 x1 x2) := ((times Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  | Co vars (plusOL2 x1 x2) := ((plus Co) (evalOp Co vars x1) (evalOp Co vars x2))  
  | Co vars zeroOL2 := (zero Co)  
  | Co vars (negOL2 x1) := ((neg Co) (evalOp Co vars x1))  
  def inductionB   {P : (CommutativeRingTerm → Type)}  : ((P oneL) → ((∀ (x1 x2 : CommutativeRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : CommutativeRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : CommutativeRingTerm) , ((P x1) → (P (negL x1)))) → (∀ (x : CommutativeRingTerm) , (P x))))))) 
  | p1l ptimesl pplusl p0l pnegl oneL := p1l  
  | p1l ptimesl pplusl p0l pnegl (timesL x1 x2) := (ptimesl _ _ (inductionB p1l ptimesl pplusl p0l pnegl x1) (inductionB p1l ptimesl pplusl p0l pnegl x2))  
  | p1l ptimesl pplusl p0l pnegl (plusL x1 x2) := (pplusl _ _ (inductionB p1l ptimesl pplusl p0l pnegl x1) (inductionB p1l ptimesl pplusl p0l pnegl x2))  
  | p1l ptimesl pplusl p0l pnegl zeroL := p0l  
  | p1l ptimesl pplusl p0l pnegl (negL x1) := (pnegl _ (inductionB p1l ptimesl pplusl p0l pnegl x1))  
  def inductionCl   {A : Type} {P : ((ClCommutativeRingTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P oneCl) → ((∀ (x1 x2 : (ClCommutativeRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClCommutativeRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClCommutativeRingTerm A)) , ((P x1) → (P (negCl x1)))) → (∀ (x : (ClCommutativeRingTerm A)) , (P x)))))))) 
  | psing p1cl ptimescl ppluscl p0cl pnegcl (sing x1) := (psing x1)  
  | psing p1cl ptimescl ppluscl p0cl pnegcl oneCl := p1cl  
  | psing p1cl ptimescl ppluscl p0cl pnegcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p1cl ptimescl ppluscl p0cl pnegcl x1) (inductionCl psing p1cl ptimescl ppluscl p0cl pnegcl x2))  
  | psing p1cl ptimescl ppluscl p0cl pnegcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p1cl ptimescl ppluscl p0cl pnegcl x1) (inductionCl psing p1cl ptimescl ppluscl p0cl pnegcl x2))  
  | psing p1cl ptimescl ppluscl p0cl pnegcl zeroCl := p0cl  
  | psing p1cl ptimescl ppluscl p0cl pnegcl (negCl x1) := (pnegcl _ (inductionCl psing p1cl ptimescl ppluscl p0cl pnegcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpCommutativeRingTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P oneOL) → ((∀ (x1 x2 : (OpCommutativeRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpCommutativeRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpCommutativeRingTerm n)) , ((P x1) → (P (negOL x1)))) → (∀ (x : (OpCommutativeRingTerm n)) , (P x)))))))) 
  | pv p1ol ptimesol pplusol p0ol pnegol (v x1) := (pv x1)  
  | pv p1ol ptimesol pplusol p0ol pnegol oneOL := p1ol  
  | pv p1ol ptimesol pplusol p0ol pnegol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p1ol ptimesol pplusol p0ol pnegol x1) (inductionOpB pv p1ol ptimesol pplusol p0ol pnegol x2))  
  | pv p1ol ptimesol pplusol p0ol pnegol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p1ol ptimesol pplusol p0ol pnegol x1) (inductionOpB pv p1ol ptimesol pplusol p0ol pnegol x2))  
  | pv p1ol ptimesol pplusol p0ol pnegol zeroOL := p0ol  
  | pv p1ol ptimesol pplusol p0ol pnegol (negOL x1) := (pnegol _ (inductionOpB pv p1ol ptimesol pplusol p0ol pnegol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpCommutativeRingTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P oneOL2) → ((∀ (x1 x2 : (OpCommutativeRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpCommutativeRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpCommutativeRingTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → (∀ (x : (OpCommutativeRingTerm2 n A)) , (P x))))))))) 
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 oneOL2 := p1ol2  
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 zeroOL2 := p0ol2  
  | pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 p1ol2 ptimesol2 pplusol2 p0ol2 pnegol2 x1))  
  def stageB  : (CommutativeRingTerm → (Staged CommutativeRingTerm))
  | oneL := (Now oneL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClCommutativeRingTerm A) → (Staged (ClCommutativeRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | oneCl := (Now oneCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpCommutativeRingTerm n) → (Staged (OpCommutativeRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | oneOL := (Now oneOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpCommutativeRingTerm2 n A) → (Staged (OpCommutativeRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | oneOL2 := (Now oneOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (oneT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A))) 
  
end CommutativeRing