import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Ring   
  structure Ring  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero)) 
  
  open Ring
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (oneP : (Prod A A))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ri1 : (Ring A1)) (Ri2 : (Ring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ri1) x1 x2)) = ((times Ri2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ri1) x1 x2)) = ((plus Ri2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ri1)) = (zero Ri2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Ri1) x1)) = ((neg Ri2) (hom x1))))
       (pres_one : (hom (one Ri1)) = (one Ri2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ri1 : (Ring A1)) (Ri2 : (Ring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ri1) x1 x2) ((times Ri2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ri1) x1 x2) ((plus Ri2) y1 y2))))))
       (interp_zero : (interp (zero Ri1) (zero Ri2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Ri1) x1) ((neg Ri2) y1)))))
       (interp_one : (interp (one Ri1) (one Ri2))) 
  
  inductive RingTerm   : Type  
     | timesL : (RingTerm → (RingTerm → RingTerm)) 
     | plusL : (RingTerm → (RingTerm → RingTerm)) 
     | zeroL : RingTerm 
     | negL : (RingTerm → RingTerm) 
     | oneL : RingTerm  
      open RingTerm 
  
  inductive ClRingTerm  (A : Type) : Type  
     | sing : (A → ClRingTerm) 
     | timesCl : (ClRingTerm → (ClRingTerm → ClRingTerm)) 
     | plusCl : (ClRingTerm → (ClRingTerm → ClRingTerm)) 
     | zeroCl : ClRingTerm 
     | negCl : (ClRingTerm → ClRingTerm) 
     | oneCl : ClRingTerm  
      open ClRingTerm 
  
  inductive OpRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRingTerm) 
     | timesOL : (OpRingTerm → (OpRingTerm → OpRingTerm)) 
     | plusOL : (OpRingTerm → (OpRingTerm → OpRingTerm)) 
     | zeroOL : OpRingTerm 
     | negOL : (OpRingTerm → OpRingTerm) 
     | oneOL : OpRingTerm  
      open OpRingTerm 
  
  inductive OpRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRingTerm2) 
     | sing2 : (A → OpRingTerm2) 
     | timesOL2 : (OpRingTerm2 → (OpRingTerm2 → OpRingTerm2)) 
     | plusOL2 : (OpRingTerm2 → (OpRingTerm2 → OpRingTerm2)) 
     | zeroOL2 : OpRingTerm2 
     | negOL2 : (OpRingTerm2 → OpRingTerm2) 
     | oneOL2 : OpRingTerm2  
      open OpRingTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRingTerm A) → (ClRingTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRingTerm n) → (OpRingTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRingTerm2 n A) → (OpRingTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Ring A) → (RingTerm → A)) 
  | Ri (timesL x1 x2) := ((times Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri (plusL x1 x2) := ((plus Ri) (evalB Ri x1) (evalB Ri x2))  
  | Ri zeroL := (zero Ri)  
  | Ri (negL x1) := ((neg Ri) (evalB Ri x1))  
  | Ri oneL := (one Ri)  
  def evalCl   {A : Type}  : ((Ring A) → ((ClRingTerm A) → A)) 
  | Ri (sing x1) := x1  
  | Ri (timesCl x1 x2) := ((times Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri (plusCl x1 x2) := ((plus Ri) (evalCl Ri x1) (evalCl Ri x2))  
  | Ri zeroCl := (zero Ri)  
  | Ri (negCl x1) := ((neg Ri) (evalCl Ri x1))  
  | Ri oneCl := (one Ri)  
  def evalOpB   {A : Type} (n : ℕ)  : ((Ring A) → ((vector A n) → ((OpRingTerm n) → A))) 
  | Ri vars (v x1) := (nth vars x1)  
  | Ri vars (timesOL x1 x2) := ((times Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars (plusOL x1 x2) := ((plus Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  | Ri vars zeroOL := (zero Ri)  
  | Ri vars (negOL x1) := ((neg Ri) (evalOpB Ri vars x1))  
  | Ri vars oneOL := (one Ri)  
  def evalOp   {A : Type} (n : ℕ)  : ((Ring A) → ((vector A n) → ((OpRingTerm2 n A) → A))) 
  | Ri vars (v2 x1) := (nth vars x1)  
  | Ri vars (sing2 x1) := x1  
  | Ri vars (timesOL2 x1 x2) := ((times Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars (plusOL2 x1 x2) := ((plus Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  | Ri vars zeroOL2 := (zero Ri)  
  | Ri vars (negOL2 x1) := ((neg Ri) (evalOp Ri vars x1))  
  | Ri vars oneOL2 := (one Ri)  
  def inductionB   (P : (RingTerm → Type))  : ((∀ (x1 x2 : RingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : RingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : RingTerm) , ((P x1) → (P (negL x1)))) → ((P oneL) → (∀ (x : RingTerm) , (P x))))))) 
  | ptimesl pplusl p0l pnegl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p0l pnegl p1l x1) (inductionB ptimesl pplusl p0l pnegl p1l x2))  
  | ptimesl pplusl p0l pnegl p1l (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p0l pnegl p1l x1) (inductionB ptimesl pplusl p0l pnegl p1l x2))  
  | ptimesl pplusl p0l pnegl p1l zeroL := p0l  
  | ptimesl pplusl p0l pnegl p1l (negL x1) := (pnegl _ (inductionB ptimesl pplusl p0l pnegl p1l x1))  
  | ptimesl pplusl p0l pnegl p1l oneL := p1l  
  def inductionCl   (A : Type) (P : ((ClRingTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClRingTerm A)) , ((P x1) → (P (negCl x1)))) → ((P oneCl) → (∀ (x : (ClRingTerm A)) , (P x)))))))) 
  | psing ptimescl ppluscl p0cl pnegcl p1cl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p0cl pnegcl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p0cl pnegcl p1cl x1) (inductionCl psing ptimescl ppluscl p0cl pnegcl p1cl x2))  
  | psing ptimescl ppluscl p0cl pnegcl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p0cl pnegcl p1cl x1) (inductionCl psing ptimescl ppluscl p0cl pnegcl p1cl x2))  
  | psing ptimescl ppluscl p0cl pnegcl p1cl zeroCl := p0cl  
  | psing ptimescl ppluscl p0cl pnegcl p1cl (negCl x1) := (pnegcl _ (inductionCl psing ptimescl ppluscl p0cl pnegcl p1cl x1))  
  | psing ptimescl ppluscl p0cl pnegcl p1cl oneCl := p1cl  
  def inductionOpB   (n : ℕ) (P : ((OpRingTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpRingTerm n)) , ((P x1) → (P (negOL x1)))) → ((P oneOL) → (∀ (x : (OpRingTerm n)) , (P x)))))))) 
  | pv ptimesol pplusol p0ol pnegol p1ol (v x1) := (pv x1)  
  | pv ptimesol pplusol p0ol pnegol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p0ol pnegol p1ol x1) (inductionOpB pv ptimesol pplusol p0ol pnegol p1ol x2))  
  | pv ptimesol pplusol p0ol pnegol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p0ol pnegol p1ol x1) (inductionOpB pv ptimesol pplusol p0ol pnegol p1ol x2))  
  | pv ptimesol pplusol p0ol pnegol p1ol zeroOL := p0ol  
  | pv ptimesol pplusol p0ol pnegol p1ol (negOL x1) := (pnegol _ (inductionOpB pv ptimesol pplusol p0ol pnegol p1ol x1))  
  | pv ptimesol pplusol p0ol pnegol p1ol oneOL := p1ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRingTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpRingTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → ((P oneOL2) → (∀ (x : (OpRingTerm2 n A)) , (P x))))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 x1))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (RingTerm → (Staged RingTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  | oneL := (Now oneL)  
  def stageCl   (A : Type)  : ((ClRingTerm A) → (Staged (ClRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  | oneCl := (Now oneCl)  
  def stageOpB   (n : ℕ)  : ((OpRingTerm n) → (Staged (OpRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  | oneOL := (Now oneOL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRingTerm2 n A) → (Staged (OpRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A)))
       (oneT : (Repr A)) 
  
end Ring