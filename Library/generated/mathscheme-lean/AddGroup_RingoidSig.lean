import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AddGroup_RingoidSig   
  structure AddGroup_RingoidSig  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero))
       (times : (A → (A → A))) 
  
  open AddGroup_RingoidSig
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
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AddGroup_RingoidSig A1)) (Ad2 : (AddGroup_RingoidSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ad1)) = (zero Ad2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Ad1) x1)) = ((neg Ad2) (hom x1))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ad1) x1 x2)) = ((times Ad2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AddGroup_RingoidSig A1)) (Ad2 : (AddGroup_RingoidSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2))))))
       (interp_zero : (interp (zero Ad1) (zero Ad2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Ad1) x1) ((neg Ad2) y1)))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ad1) x1 x2) ((times Ad2) y1 y2)))))) 
  
  inductive AddGroup_RingoidSigTerm   : Type  
     | plusL : (AddGroup_RingoidSigTerm → (AddGroup_RingoidSigTerm → AddGroup_RingoidSigTerm)) 
     | zeroL : AddGroup_RingoidSigTerm 
     | negL : (AddGroup_RingoidSigTerm → AddGroup_RingoidSigTerm) 
     | timesL : (AddGroup_RingoidSigTerm → (AddGroup_RingoidSigTerm → AddGroup_RingoidSigTerm))  
      open AddGroup_RingoidSigTerm 
  
  inductive ClAddGroup_RingoidSigTerm  (A : Type) : Type  
     | sing : (A → ClAddGroup_RingoidSigTerm) 
     | plusCl : (ClAddGroup_RingoidSigTerm → (ClAddGroup_RingoidSigTerm → ClAddGroup_RingoidSigTerm)) 
     | zeroCl : ClAddGroup_RingoidSigTerm 
     | negCl : (ClAddGroup_RingoidSigTerm → ClAddGroup_RingoidSigTerm) 
     | timesCl : (ClAddGroup_RingoidSigTerm → (ClAddGroup_RingoidSigTerm → ClAddGroup_RingoidSigTerm))  
      open ClAddGroup_RingoidSigTerm 
  
  inductive OpAddGroup_RingoidSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAddGroup_RingoidSigTerm) 
     | plusOL : (OpAddGroup_RingoidSigTerm → (OpAddGroup_RingoidSigTerm → OpAddGroup_RingoidSigTerm)) 
     | zeroOL : OpAddGroup_RingoidSigTerm 
     | negOL : (OpAddGroup_RingoidSigTerm → OpAddGroup_RingoidSigTerm) 
     | timesOL : (OpAddGroup_RingoidSigTerm → (OpAddGroup_RingoidSigTerm → OpAddGroup_RingoidSigTerm))  
      open OpAddGroup_RingoidSigTerm 
  
  inductive OpAddGroup_RingoidSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAddGroup_RingoidSigTerm2) 
     | sing2 : (A → OpAddGroup_RingoidSigTerm2) 
     | plusOL2 : (OpAddGroup_RingoidSigTerm2 → (OpAddGroup_RingoidSigTerm2 → OpAddGroup_RingoidSigTerm2)) 
     | zeroOL2 : OpAddGroup_RingoidSigTerm2 
     | negOL2 : (OpAddGroup_RingoidSigTerm2 → OpAddGroup_RingoidSigTerm2) 
     | timesOL2 : (OpAddGroup_RingoidSigTerm2 → (OpAddGroup_RingoidSigTerm2 → OpAddGroup_RingoidSigTerm2))  
      open OpAddGroup_RingoidSigTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAddGroup_RingoidSigTerm A) → (ClAddGroup_RingoidSigTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAddGroup_RingoidSigTerm n) → (OpAddGroup_RingoidSigTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAddGroup_RingoidSigTerm2 n A) → (OpAddGroup_RingoidSigTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AddGroup_RingoidSig A) → (AddGroup_RingoidSigTerm → A)) 
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  | Ad zeroL := (zero Ad)  
  | Ad (negL x1) := ((neg Ad) (evalB Ad x1))  
  | Ad (timesL x1 x2) := ((times Ad) (evalB Ad x1) (evalB Ad x2))  
  def evalCl   {A : Type}  : ((AddGroup_RingoidSig A) → ((ClAddGroup_RingoidSigTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  | Ad zeroCl := (zero Ad)  
  | Ad (negCl x1) := ((neg Ad) (evalCl Ad x1))  
  | Ad (timesCl x1 x2) := ((times Ad) (evalCl Ad x1) (evalCl Ad x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AddGroup_RingoidSig A) → ((vector A n) → ((OpAddGroup_RingoidSigTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  | Ad vars zeroOL := (zero Ad)  
  | Ad vars (negOL x1) := ((neg Ad) (evalOpB Ad vars x1))  
  | Ad vars (timesOL x1 x2) := ((times Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((AddGroup_RingoidSig A) → ((vector A n) → ((OpAddGroup_RingoidSigTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  | Ad vars zeroOL2 := (zero Ad)  
  | Ad vars (negOL2 x1) := ((neg Ad) (evalOp Ad vars x1))  
  | Ad vars (timesOL2 x1 x2) := ((times Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  def inductionB   (P : (AddGroup_RingoidSigTerm → Type))  : ((∀ (x1 x2 : AddGroup_RingoidSigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : AddGroup_RingoidSigTerm) , ((P x1) → (P (negL x1)))) → ((∀ (x1 x2 : AddGroup_RingoidSigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : AddGroup_RingoidSigTerm) , (P x)))))) 
  | pplusl p0l pnegl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l pnegl ptimesl x1) (inductionB pplusl p0l pnegl ptimesl x2))  
  | pplusl p0l pnegl ptimesl zeroL := p0l  
  | pplusl p0l pnegl ptimesl (negL x1) := (pnegl _ (inductionB pplusl p0l pnegl ptimesl x1))  
  | pplusl p0l pnegl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl p0l pnegl ptimesl x1) (inductionB pplusl p0l pnegl ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClAddGroup_RingoidSigTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAddGroup_RingoidSigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClAddGroup_RingoidSigTerm A)) , ((P x1) → (P (negCl x1)))) → ((∀ (x1 x2 : (ClAddGroup_RingoidSigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClAddGroup_RingoidSigTerm A)) , (P x))))))) 
  | psing ppluscl p0cl pnegcl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl p0cl pnegcl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl pnegcl ptimescl x1) (inductionCl psing ppluscl p0cl pnegcl ptimescl x2))  
  | psing ppluscl p0cl pnegcl ptimescl zeroCl := p0cl  
  | psing ppluscl p0cl pnegcl ptimescl (negCl x1) := (pnegcl _ (inductionCl psing ppluscl p0cl pnegcl ptimescl x1))  
  | psing ppluscl p0cl pnegcl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl p0cl pnegcl ptimescl x1) (inductionCl psing ppluscl p0cl pnegcl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAddGroup_RingoidSigTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAddGroup_RingoidSigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpAddGroup_RingoidSigTerm n)) , ((P x1) → (P (negOL x1)))) → ((∀ (x1 x2 : (OpAddGroup_RingoidSigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpAddGroup_RingoidSigTerm n)) , (P x))))))) 
  | pv pplusol p0ol pnegol ptimesol (v x1) := (pv x1)  
  | pv pplusol p0ol pnegol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol pnegol ptimesol x1) (inductionOpB pv pplusol p0ol pnegol ptimesol x2))  
  | pv pplusol p0ol pnegol ptimesol zeroOL := p0ol  
  | pv pplusol p0ol pnegol ptimesol (negOL x1) := (pnegol _ (inductionOpB pv pplusol p0ol pnegol ptimesol x1))  
  | pv pplusol p0ol pnegol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol p0ol pnegol ptimesol x1) (inductionOpB pv pplusol p0ol pnegol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAddGroup_RingoidSigTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAddGroup_RingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpAddGroup_RingoidSigTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → ((∀ (x1 x2 : (OpAddGroup_RingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpAddGroup_RingoidSigTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x1))  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 ptimesol2 x2))  
  def stageB  : (AddGroup_RingoidSigTerm → (Staged AddGroup_RingoidSigTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAddGroup_RingoidSigTerm A) → (Staged (ClAddGroup_RingoidSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAddGroup_RingoidSigTerm n) → (Staged (OpAddGroup_RingoidSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAddGroup_RingoidSigTerm2 n A) → (Staged (OpAddGroup_RingoidSigTerm2 n A))) 
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
  
end AddGroup_RingoidSig