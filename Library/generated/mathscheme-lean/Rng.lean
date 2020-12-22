import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Rng   
  structure Rng  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero))
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open Rng
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Rn1 : (Rng A1)) (Rn2 : (Rng A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Rn1) x1 x2)) = ((plus Rn2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Rn1)) = (zero Rn2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Rn1) x1)) = ((neg Rn2) (hom x1))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Rn1) x1 x2)) = ((times Rn2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Rn1 : (Rng A1)) (Rn2 : (Rng A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Rn1) x1 x2) ((plus Rn2) y1 y2))))))
       (interp_zero : (interp (zero Rn1) (zero Rn2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Rn1) x1) ((neg Rn2) y1)))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Rn1) x1 x2) ((times Rn2) y1 y2)))))) 
  
  inductive RngTerm   : Type  
     | plusL : (RngTerm → (RngTerm → RngTerm)) 
     | zeroL : RngTerm 
     | negL : (RngTerm → RngTerm) 
     | timesL : (RngTerm → (RngTerm → RngTerm))  
      open RngTerm 
  
  inductive ClRngTerm  (A : Type) : Type  
     | sing : (A → ClRngTerm) 
     | plusCl : (ClRngTerm → (ClRngTerm → ClRngTerm)) 
     | zeroCl : ClRngTerm 
     | negCl : (ClRngTerm → ClRngTerm) 
     | timesCl : (ClRngTerm → (ClRngTerm → ClRngTerm))  
      open ClRngTerm 
  
  inductive OpRngTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpRngTerm) 
     | plusOL : (OpRngTerm → (OpRngTerm → OpRngTerm)) 
     | zeroOL : OpRngTerm 
     | negOL : (OpRngTerm → OpRngTerm) 
     | timesOL : (OpRngTerm → (OpRngTerm → OpRngTerm))  
      open OpRngTerm 
  
  inductive OpRngTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpRngTerm2) 
     | sing2 : (A → OpRngTerm2) 
     | plusOL2 : (OpRngTerm2 → (OpRngTerm2 → OpRngTerm2)) 
     | zeroOL2 : OpRngTerm2 
     | negOL2 : (OpRngTerm2 → OpRngTerm2) 
     | timesOL2 : (OpRngTerm2 → (OpRngTerm2 → OpRngTerm2))  
      open OpRngTerm2 
  
  def simplifyCl   (A : Type)  : ((ClRngTerm A) → (ClRngTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpRngTerm n) → (OpRngTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpRngTerm2 n A) → (OpRngTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((Rng A) → (RngTerm → A)) 
  | Rn (plusL x1 x2) := ((plus Rn) (evalB Rn x1) (evalB Rn x2))  
  | Rn zeroL := (zero Rn)  
  | Rn (negL x1) := ((neg Rn) (evalB Rn x1))  
  | Rn (timesL x1 x2) := ((times Rn) (evalB Rn x1) (evalB Rn x2))  
  def evalCl   {A : Type}  : ((Rng A) → ((ClRngTerm A) → A)) 
  | Rn (sing x1) := x1  
  | Rn (plusCl x1 x2) := ((plus Rn) (evalCl Rn x1) (evalCl Rn x2))  
  | Rn zeroCl := (zero Rn)  
  | Rn (negCl x1) := ((neg Rn) (evalCl Rn x1))  
  | Rn (timesCl x1 x2) := ((times Rn) (evalCl Rn x1) (evalCl Rn x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((Rng A) → ((vector A n) → ((OpRngTerm n) → A))) 
  | Rn vars (v x1) := (nth vars x1)  
  | Rn vars (plusOL x1 x2) := ((plus Rn) (evalOpB Rn vars x1) (evalOpB Rn vars x2))  
  | Rn vars zeroOL := (zero Rn)  
  | Rn vars (negOL x1) := ((neg Rn) (evalOpB Rn vars x1))  
  | Rn vars (timesOL x1 x2) := ((times Rn) (evalOpB Rn vars x1) (evalOpB Rn vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((Rng A) → ((vector A n) → ((OpRngTerm2 n A) → A))) 
  | Rn vars (v2 x1) := (nth vars x1)  
  | Rn vars (sing2 x1) := x1  
  | Rn vars (plusOL2 x1 x2) := ((plus Rn) (evalOp Rn vars x1) (evalOp Rn vars x2))  
  | Rn vars zeroOL2 := (zero Rn)  
  | Rn vars (negOL2 x1) := ((neg Rn) (evalOp Rn vars x1))  
  | Rn vars (timesOL2 x1 x2) := ((times Rn) (evalOp Rn vars x1) (evalOp Rn vars x2))  
  def inductionB   (P : (RngTerm → Type))  : ((∀ (x1 x2 : RngTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : RngTerm) , ((P x1) → (P (negL x1)))) → ((∀ (x1 x2 : RngTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : RngTerm) , (P x)))))) 
  | pplusl p0l pnegl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l pnegl ptimesl x1) (inductionB pplusl p0l pnegl ptimesl x2))  
  | pplusl p0l pnegl ptimesl zeroL := p0l  
  | pplusl p0l pnegl ptimesl (negL x1) := (pnegl _ (inductionB pplusl p0l pnegl ptimesl x1))  
  | pplusl p0l pnegl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl p0l pnegl ptimesl x1) (inductionB pplusl p0l pnegl ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClRngTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClRngTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClRngTerm A)) , ((P x1) → (P (negCl x1)))) → ((∀ (x1 x2 : (ClRngTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClRngTerm A)) , (P x))))))) 
  | psing ppluscl p0cl pnegcl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl p0cl pnegcl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl pnegcl ptimescl x1) (inductionCl psing ppluscl p0cl pnegcl ptimescl x2))  
  | psing ppluscl p0cl pnegcl ptimescl zeroCl := p0cl  
  | psing ppluscl p0cl pnegcl ptimescl (negCl x1) := (pnegcl _ (inductionCl psing ppluscl p0cl pnegcl ptimescl x1))  
  | psing ppluscl p0cl pnegcl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl p0cl pnegcl ptimescl x1) (inductionCl psing ppluscl p0cl pnegcl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpRngTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpRngTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpRngTerm n)) , ((P x1) → (P (negOL x1)))) → ((∀ (x1 x2 : (OpRngTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpRngTerm n)) , (P x))))))) 
  | pv pplusol p0ol pnegol ptimesol (v x1) := (pv x1)  
  | pv pplusol p0ol pnegol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol pnegol ptimesol x1) (inductionOpB pv pplusol p0ol pnegol ptimesol x2))  
  | pv pplusol p0ol pnegol ptimesol zeroOL := p0ol  
  | pv pplusol p0ol pnegol ptimesol (negOL x1) := (pnegol _ (inductionOpB pv pplusol p0ol pnegol ptimesol x1))  
  | pv pplusol p0ol pnegol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol p0ol pnegol ptimesol x1) (inductionOpB pv pplusol p0ol pnegol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpRngTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpRngTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpRngTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → ((∀ (x1 x2 : (OpRngTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpRngTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x1))  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x2))  
  def stageB  : (RngTerm → (Staged RngTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClRngTerm A) → (Staged (ClRngTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpRngTerm n) → (Staged (OpRngTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpRngTerm2 n A) → (Staged (OpRngTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A)))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end Rng