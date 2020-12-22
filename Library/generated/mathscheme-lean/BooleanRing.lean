import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section BooleanRing   
  structure BooleanRing  (A : Type) : Type := 
       (times : (A → (A → A)))
       (one : A)
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
       (idempotent_times : (∀ {x : A} , (times x x) = x)) 
  
  open BooleanRing
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (oneS : AS)
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
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
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Bo1 : (BooleanRing A1)) (Bo2 : (BooleanRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Bo1) x1 x2)) = ((times Bo2) (hom x1) (hom x2))))
       (pres_one : (hom (one Bo1)) = (one Bo2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Bo1) x1 x2)) = ((plus Bo2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Bo1)) = (zero Bo2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Bo1) x1)) = ((neg Bo2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Bo1 : (BooleanRing A1)) (Bo2 : (BooleanRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Bo1) x1 x2) ((times Bo2) y1 y2))))))
       (interp_one : (interp (one Bo1) (one Bo2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Bo1) x1 x2) ((plus Bo2) y1 y2))))))
       (interp_zero : (interp (zero Bo1) (zero Bo2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Bo1) x1) ((neg Bo2) y1))))) 
  
  inductive BooleanRingTerm   : Type  
     | timesL : (BooleanRingTerm → (BooleanRingTerm → BooleanRingTerm)) 
     | oneL : BooleanRingTerm 
     | plusL : (BooleanRingTerm → (BooleanRingTerm → BooleanRingTerm)) 
     | zeroL : BooleanRingTerm 
     | negL : (BooleanRingTerm → BooleanRingTerm)  
      open BooleanRingTerm 
  
  inductive ClBooleanRingTerm  (A : Type) : Type  
     | sing : (A → ClBooleanRingTerm) 
     | timesCl : (ClBooleanRingTerm → (ClBooleanRingTerm → ClBooleanRingTerm)) 
     | oneCl : ClBooleanRingTerm 
     | plusCl : (ClBooleanRingTerm → (ClBooleanRingTerm → ClBooleanRingTerm)) 
     | zeroCl : ClBooleanRingTerm 
     | negCl : (ClBooleanRingTerm → ClBooleanRingTerm)  
      open ClBooleanRingTerm 
  
  inductive OpBooleanRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpBooleanRingTerm) 
     | timesOL : (OpBooleanRingTerm → (OpBooleanRingTerm → OpBooleanRingTerm)) 
     | oneOL : OpBooleanRingTerm 
     | plusOL : (OpBooleanRingTerm → (OpBooleanRingTerm → OpBooleanRingTerm)) 
     | zeroOL : OpBooleanRingTerm 
     | negOL : (OpBooleanRingTerm → OpBooleanRingTerm)  
      open OpBooleanRingTerm 
  
  inductive OpBooleanRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpBooleanRingTerm2) 
     | sing2 : (A → OpBooleanRingTerm2) 
     | timesOL2 : (OpBooleanRingTerm2 → (OpBooleanRingTerm2 → OpBooleanRingTerm2)) 
     | oneOL2 : OpBooleanRingTerm2 
     | plusOL2 : (OpBooleanRingTerm2 → (OpBooleanRingTerm2 → OpBooleanRingTerm2)) 
     | zeroOL2 : OpBooleanRingTerm2 
     | negOL2 : (OpBooleanRingTerm2 → OpBooleanRingTerm2)  
      open OpBooleanRingTerm2 
  
  def simplifyCl   (A : Type)  : ((ClBooleanRingTerm A) → (ClBooleanRingTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpBooleanRingTerm n) → (OpBooleanRingTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpBooleanRingTerm2 n A) → (OpBooleanRingTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((BooleanRing A) → (BooleanRingTerm → A)) 
  | Bo (timesL x1 x2) := ((times Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo oneL := (one Bo)  
  | Bo (plusL x1 x2) := ((plus Bo) (evalB Bo x1) (evalB Bo x2))  
  | Bo zeroL := (zero Bo)  
  | Bo (negL x1) := ((neg Bo) (evalB Bo x1))  
  def evalCl   {A : Type}  : ((BooleanRing A) → ((ClBooleanRingTerm A) → A)) 
  | Bo (sing x1) := x1  
  | Bo (timesCl x1 x2) := ((times Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo oneCl := (one Bo)  
  | Bo (plusCl x1 x2) := ((plus Bo) (evalCl Bo x1) (evalCl Bo x2))  
  | Bo zeroCl := (zero Bo)  
  | Bo (negCl x1) := ((neg Bo) (evalCl Bo x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((BooleanRing A) → ((vector A n) → ((OpBooleanRingTerm n) → A))) 
  | Bo vars (v x1) := (nth vars x1)  
  | Bo vars (timesOL x1 x2) := ((times Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars oneOL := (one Bo)  
  | Bo vars (plusOL x1 x2) := ((plus Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  | Bo vars zeroOL := (zero Bo)  
  | Bo vars (negOL x1) := ((neg Bo) (evalOpB Bo vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((BooleanRing A) → ((vector A n) → ((OpBooleanRingTerm2 n A) → A))) 
  | Bo vars (v2 x1) := (nth vars x1)  
  | Bo vars (sing2 x1) := x1  
  | Bo vars (timesOL2 x1 x2) := ((times Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars oneOL2 := (one Bo)  
  | Bo vars (plusOL2 x1 x2) := ((plus Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  | Bo vars zeroOL2 := (zero Bo)  
  | Bo vars (negOL2 x1) := ((neg Bo) (evalOp Bo vars x1))  
  def inductionB   (P : (BooleanRingTerm → Type))  : ((∀ (x1 x2 : BooleanRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → ((∀ (x1 x2 : BooleanRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : BooleanRingTerm) , ((P x1) → (P (negL x1)))) → (∀ (x : BooleanRingTerm) , (P x))))))) 
  | ptimesl p1l pplusl p0l pnegl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl p1l pplusl p0l pnegl x1) (inductionB ptimesl p1l pplusl p0l pnegl x2))  
  | ptimesl p1l pplusl p0l pnegl oneL := p1l  
  | ptimesl p1l pplusl p0l pnegl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl p1l pplusl p0l pnegl x1) (inductionB ptimesl p1l pplusl p0l pnegl x2))  
  | ptimesl p1l pplusl p0l pnegl zeroL := p0l  
  | ptimesl p1l pplusl p0l pnegl (negL x1) := (pnegl _ (inductionB ptimesl p1l pplusl p0l pnegl x1))  
  def inductionCl   (A : Type) (P : ((ClBooleanRingTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClBooleanRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → ((∀ (x1 x2 : (ClBooleanRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClBooleanRingTerm A)) , ((P x1) → (P (negCl x1)))) → (∀ (x : (ClBooleanRingTerm A)) , (P x)))))))) 
  | psing ptimescl p1cl ppluscl p0cl pnegcl (sing x1) := (psing x1)  
  | psing ptimescl p1cl ppluscl p0cl pnegcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl p1cl ppluscl p0cl pnegcl x1) (inductionCl psing ptimescl p1cl ppluscl p0cl pnegcl x2))  
  | psing ptimescl p1cl ppluscl p0cl pnegcl oneCl := p1cl  
  | psing ptimescl p1cl ppluscl p0cl pnegcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl p1cl ppluscl p0cl pnegcl x1) (inductionCl psing ptimescl p1cl ppluscl p0cl pnegcl x2))  
  | psing ptimescl p1cl ppluscl p0cl pnegcl zeroCl := p0cl  
  | psing ptimescl p1cl ppluscl p0cl pnegcl (negCl x1) := (pnegcl _ (inductionCl psing ptimescl p1cl ppluscl p0cl pnegcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpBooleanRingTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpBooleanRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → ((∀ (x1 x2 : (OpBooleanRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpBooleanRingTerm n)) , ((P x1) → (P (negOL x1)))) → (∀ (x : (OpBooleanRingTerm n)) , (P x)))))))) 
  | pv ptimesol p1ol pplusol p0ol pnegol (v x1) := (pv x1)  
  | pv ptimesol p1ol pplusol p0ol pnegol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol p1ol pplusol p0ol pnegol x1) (inductionOpB pv ptimesol p1ol pplusol p0ol pnegol x2))  
  | pv ptimesol p1ol pplusol p0ol pnegol oneOL := p1ol  
  | pv ptimesol p1ol pplusol p0ol pnegol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol p1ol pplusol p0ol pnegol x1) (inductionOpB pv ptimesol p1ol pplusol p0ol pnegol x2))  
  | pv ptimesol p1ol pplusol p0ol pnegol zeroOL := p0ol  
  | pv ptimesol p1ol pplusol p0ol pnegol (negOL x1) := (pnegol _ (inductionOpB pv ptimesol p1ol pplusol p0ol pnegol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpBooleanRingTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpBooleanRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 x2 : (OpBooleanRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpBooleanRingTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → (∀ (x : (OpBooleanRingTerm2 n A)) , (P x))))))))) 
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 ptimesol2 p1ol2 pplusol2 p0ol2 pnegol2 x1))  
  def stageB  : (BooleanRingTerm → (Staged BooleanRingTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClBooleanRingTerm A) → (Staged (ClBooleanRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpBooleanRingTerm n) → (Staged (OpBooleanRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpBooleanRingTerm2 n A) → (Staged (OpBooleanRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A))) 
  
end BooleanRing