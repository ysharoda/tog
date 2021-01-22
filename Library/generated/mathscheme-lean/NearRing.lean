import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section NearRing   
  structure NearRing  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x)))) 
  
  open NearRing
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ne1 : (NearRing A1)) (Ne2 : (NearRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ne1) x1 x2)) = ((times Ne2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ne1) x1 x2)) = ((plus Ne2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ne1)) = (zero Ne2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Ne1) x1)) = ((neg Ne2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ne1 : (NearRing A1)) (Ne2 : (NearRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ne1) x1 x2) ((times Ne2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ne1) x1 x2) ((plus Ne2) y1 y2))))))
       (interp_zero : (interp (zero Ne1) (zero Ne2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Ne1) x1) ((neg Ne2) y1))))) 
  
  inductive NearRingTerm   : Type  
     | timesL : (NearRingTerm → (NearRingTerm → NearRingTerm)) 
     | plusL : (NearRingTerm → (NearRingTerm → NearRingTerm)) 
     | zeroL : NearRingTerm 
     | negL : (NearRingTerm → NearRingTerm)  
      open NearRingTerm 
  
  inductive ClNearRingTerm  (A : Type) : Type  
     | sing : (A → ClNearRingTerm) 
     | timesCl : (ClNearRingTerm → (ClNearRingTerm → ClNearRingTerm)) 
     | plusCl : (ClNearRingTerm → (ClNearRingTerm → ClNearRingTerm)) 
     | zeroCl : ClNearRingTerm 
     | negCl : (ClNearRingTerm → ClNearRingTerm)  
      open ClNearRingTerm 
  
  inductive OpNearRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpNearRingTerm) 
     | timesOL : (OpNearRingTerm → (OpNearRingTerm → OpNearRingTerm)) 
     | plusOL : (OpNearRingTerm → (OpNearRingTerm → OpNearRingTerm)) 
     | zeroOL : OpNearRingTerm 
     | negOL : (OpNearRingTerm → OpNearRingTerm)  
      open OpNearRingTerm 
  
  inductive OpNearRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpNearRingTerm2) 
     | sing2 : (A → OpNearRingTerm2) 
     | timesOL2 : (OpNearRingTerm2 → (OpNearRingTerm2 → OpNearRingTerm2)) 
     | plusOL2 : (OpNearRingTerm2 → (OpNearRingTerm2 → OpNearRingTerm2)) 
     | zeroOL2 : OpNearRingTerm2 
     | negOL2 : (OpNearRingTerm2 → OpNearRingTerm2)  
      open OpNearRingTerm2 
  
  def simplifyCl   {A : Type}  : ((ClNearRingTerm A) → (ClNearRingTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpNearRingTerm n) → (OpNearRingTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpNearRingTerm2 n A) → (OpNearRingTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((NearRing A) → (NearRingTerm → A)) 
  | Ne (timesL x1 x2) := ((times Ne) (evalB Ne x1) (evalB Ne x2))  
  | Ne (plusL x1 x2) := ((plus Ne) (evalB Ne x1) (evalB Ne x2))  
  | Ne zeroL := (zero Ne)  
  | Ne (negL x1) := ((neg Ne) (evalB Ne x1))  
  def evalCl   {A : Type}  : ((NearRing A) → ((ClNearRingTerm A) → A)) 
  | Ne (sing x1) := x1  
  | Ne (timesCl x1 x2) := ((times Ne) (evalCl Ne x1) (evalCl Ne x2))  
  | Ne (plusCl x1 x2) := ((plus Ne) (evalCl Ne x1) (evalCl Ne x2))  
  | Ne zeroCl := (zero Ne)  
  | Ne (negCl x1) := ((neg Ne) (evalCl Ne x1))  
  def evalOpB   {A : Type} {n : ℕ}  : ((NearRing A) → ((vector A n) → ((OpNearRingTerm n) → A))) 
  | Ne vars (v x1) := (nth vars x1)  
  | Ne vars (timesOL x1 x2) := ((times Ne) (evalOpB Ne vars x1) (evalOpB Ne vars x2))  
  | Ne vars (plusOL x1 x2) := ((plus Ne) (evalOpB Ne vars x1) (evalOpB Ne vars x2))  
  | Ne vars zeroOL := (zero Ne)  
  | Ne vars (negOL x1) := ((neg Ne) (evalOpB Ne vars x1))  
  def evalOp   {A : Type} {n : ℕ}  : ((NearRing A) → ((vector A n) → ((OpNearRingTerm2 n A) → A))) 
  | Ne vars (v2 x1) := (nth vars x1)  
  | Ne vars (sing2 x1) := x1  
  | Ne vars (timesOL2 x1 x2) := ((times Ne) (evalOp Ne vars x1) (evalOp Ne vars x2))  
  | Ne vars (plusOL2 x1 x2) := ((plus Ne) (evalOp Ne vars x1) (evalOp Ne vars x2))  
  | Ne vars zeroOL2 := (zero Ne)  
  | Ne vars (negOL2 x1) := ((neg Ne) (evalOp Ne vars x1))  
  def inductionB   {P : (NearRingTerm → Type)}  : ((∀ (x1 x2 : NearRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : NearRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : NearRingTerm) , ((P x1) → (P (negL x1)))) → (∀ (x : NearRingTerm) , (P x)))))) 
  | ptimesl pplusl p0l pnegl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p0l pnegl x1) (inductionB ptimesl pplusl p0l pnegl x2))  
  | ptimesl pplusl p0l pnegl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p0l pnegl x1) (inductionB ptimesl pplusl p0l pnegl x2))  
  | ptimesl pplusl p0l pnegl zeroL := p0l  
  | ptimesl pplusl p0l pnegl (negL x1) := (pnegl _ (inductionB ptimesl pplusl p0l pnegl x1))  
  def inductionCl   {A : Type} {P : ((ClNearRingTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClNearRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClNearRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClNearRingTerm A)) , ((P x1) → (P (negCl x1)))) → (∀ (x : (ClNearRingTerm A)) , (P x))))))) 
  | psing ptimescl ppluscl p0cl pnegcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p0cl pnegcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p0cl pnegcl x1) (inductionCl psing ptimescl ppluscl p0cl pnegcl x2))  
  | psing ptimescl ppluscl p0cl pnegcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p0cl pnegcl x1) (inductionCl psing ptimescl ppluscl p0cl pnegcl x2))  
  | psing ptimescl ppluscl p0cl pnegcl zeroCl := p0cl  
  | psing ptimescl ppluscl p0cl pnegcl (negCl x1) := (pnegcl _ (inductionCl psing ptimescl ppluscl p0cl pnegcl x1))  
  def inductionOpB   {n : ℕ} {P : ((OpNearRingTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpNearRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpNearRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpNearRingTerm n)) , ((P x1) → (P (negOL x1)))) → (∀ (x : (OpNearRingTerm n)) , (P x))))))) 
  | pv ptimesol pplusol p0ol pnegol (v x1) := (pv x1)  
  | pv ptimesol pplusol p0ol pnegol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p0ol pnegol x1) (inductionOpB pv ptimesol pplusol p0ol pnegol x2))  
  | pv ptimesol pplusol p0ol pnegol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p0ol pnegol x1) (inductionOpB pv ptimesol pplusol p0ol pnegol x2))  
  | pv ptimesol pplusol p0ol pnegol zeroOL := p0ol  
  | pv ptimesol pplusol p0ol pnegol (negOL x1) := (pnegol _ (inductionOpB pv ptimesol pplusol p0ol pnegol x1))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpNearRingTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpNearRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpNearRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpNearRingTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → (∀ (x : (OpNearRingTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p0ol2 pnegol2 x1))  
  def stageB  : (NearRingTerm → (Staged NearRingTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  def stageCl   {A : Type}  : ((ClNearRingTerm A) → (Staged (ClNearRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  def stageOpB   {n : ℕ}  : ((OpNearRingTerm n) → (Staged (OpNearRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpNearRingTerm2 n A) → (Staged (OpNearRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A))) 
  
end NearRing