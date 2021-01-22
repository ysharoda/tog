import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LieRing   
  structure LieRing  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (times : (A → (A → A)))
       (jacobian_times_plus : (∀ {x y z : A} , (plus (plus (times x (times y z)) (times y (times z x))) (times z (times x y))) = zero))
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
       (antiCommutative : (∀ {x y : A} , (times x y) = (neg (times y x)))) 
  
  open LieRing
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS)))
       (negS : (AS → AS))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (negP : ((Prod A A) → (Prod A A)))
       (oneP : (Prod A A))
       (jacobian_times_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP (timesP xP (timesP yP zP)) (timesP yP (timesP zP xP))) (timesP zP (timesP xP yP))) = zeroP))
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
       (antiCommutativeP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (negP (timesP yP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Li1 : (LieRing A1)) (Li2 : (LieRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Li1)) = (zero Li2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Li1) x1 x2)) = ((plus Li2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Li1) x1 x2)) = ((times Li2) (hom x1) (hom x2))))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Li1) x1)) = ((neg Li2) (hom x1))))
       (pres_one : (hom (one Li1)) = (one Li2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Li1 : (LieRing A1)) (Li2 : (LieRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Li1) (zero Li2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Li1) x1 x2) ((plus Li2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Li1) x1 x2) ((times Li2) y1 y2))))))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Li1) x1) ((neg Li2) y1)))))
       (interp_one : (interp (one Li1) (one Li2))) 
  
  inductive LieRingTerm   : Type  
     | zeroL : LieRingTerm 
     | plusL : (LieRingTerm → (LieRingTerm → LieRingTerm)) 
     | timesL : (LieRingTerm → (LieRingTerm → LieRingTerm)) 
     | negL : (LieRingTerm → LieRingTerm) 
     | oneL : LieRingTerm  
      open LieRingTerm 
  
  inductive ClLieRingTerm  (A : Type) : Type  
     | sing : (A → ClLieRingTerm) 
     | zeroCl : ClLieRingTerm 
     | plusCl : (ClLieRingTerm → (ClLieRingTerm → ClLieRingTerm)) 
     | timesCl : (ClLieRingTerm → (ClLieRingTerm → ClLieRingTerm)) 
     | negCl : (ClLieRingTerm → ClLieRingTerm) 
     | oneCl : ClLieRingTerm  
      open ClLieRingTerm 
  
  inductive OpLieRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLieRingTerm) 
     | zeroOL : OpLieRingTerm 
     | plusOL : (OpLieRingTerm → (OpLieRingTerm → OpLieRingTerm)) 
     | timesOL : (OpLieRingTerm → (OpLieRingTerm → OpLieRingTerm)) 
     | negOL : (OpLieRingTerm → OpLieRingTerm) 
     | oneOL : OpLieRingTerm  
      open OpLieRingTerm 
  
  inductive OpLieRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLieRingTerm2) 
     | sing2 : (A → OpLieRingTerm2) 
     | zeroOL2 : OpLieRingTerm2 
     | plusOL2 : (OpLieRingTerm2 → (OpLieRingTerm2 → OpLieRingTerm2)) 
     | timesOL2 : (OpLieRingTerm2 → (OpLieRingTerm2 → OpLieRingTerm2)) 
     | negOL2 : (OpLieRingTerm2 → OpLieRingTerm2) 
     | oneOL2 : OpLieRingTerm2  
      open OpLieRingTerm2 
  
  def simplifyCl   {A : Type}  : ((ClLieRingTerm A) → (ClLieRingTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (negCl (timesCl y x)) := (timesCl x y)  
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLieRingTerm n) → (OpLieRingTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (negOL (timesOL y x)) := (timesOL x y)  
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLieRingTerm2 n A) → (OpLieRingTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (negOL2 (timesOL2 y x)) := (timesOL2 x y)  
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LieRing A) → (LieRingTerm → A)) 
  | Li zeroL := (zero Li)  
  | Li (plusL x1 x2) := ((plus Li) (evalB Li x1) (evalB Li x2))  
  | Li (timesL x1 x2) := ((times Li) (evalB Li x1) (evalB Li x2))  
  | Li (negL x1) := ((neg Li) (evalB Li x1))  
  | Li oneL := (one Li)  
  def evalCl   {A : Type}  : ((LieRing A) → ((ClLieRingTerm A) → A)) 
  | Li (sing x1) := x1  
  | Li zeroCl := (zero Li)  
  | Li (plusCl x1 x2) := ((plus Li) (evalCl Li x1) (evalCl Li x2))  
  | Li (timesCl x1 x2) := ((times Li) (evalCl Li x1) (evalCl Li x2))  
  | Li (negCl x1) := ((neg Li) (evalCl Li x1))  
  | Li oneCl := (one Li)  
  def evalOpB   {A : Type} {n : ℕ}  : ((LieRing A) → ((vector A n) → ((OpLieRingTerm n) → A))) 
  | Li vars (v x1) := (nth vars x1)  
  | Li vars zeroOL := (zero Li)  
  | Li vars (plusOL x1 x2) := ((plus Li) (evalOpB Li vars x1) (evalOpB Li vars x2))  
  | Li vars (timesOL x1 x2) := ((times Li) (evalOpB Li vars x1) (evalOpB Li vars x2))  
  | Li vars (negOL x1) := ((neg Li) (evalOpB Li vars x1))  
  | Li vars oneOL := (one Li)  
  def evalOp   {A : Type} {n : ℕ}  : ((LieRing A) → ((vector A n) → ((OpLieRingTerm2 n A) → A))) 
  | Li vars (v2 x1) := (nth vars x1)  
  | Li vars (sing2 x1) := x1  
  | Li vars zeroOL2 := (zero Li)  
  | Li vars (plusOL2 x1 x2) := ((plus Li) (evalOp Li vars x1) (evalOp Li vars x2))  
  | Li vars (timesOL2 x1 x2) := ((times Li) (evalOp Li vars x1) (evalOp Li vars x2))  
  | Li vars (negOL2 x1) := ((neg Li) (evalOp Li vars x1))  
  | Li vars oneOL2 := (one Li)  
  def inductionB   {P : (LieRingTerm → Type)}  : ((P zeroL) → ((∀ (x1 x2 : LieRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : LieRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 : LieRingTerm) , ((P x1) → (P (negL x1)))) → ((P oneL) → (∀ (x : LieRingTerm) , (P x))))))) 
  | p0l pplusl ptimesl pnegl p1l zeroL := p0l  
  | p0l pplusl ptimesl pnegl p1l (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl ptimesl pnegl p1l x1) (inductionB p0l pplusl ptimesl pnegl p1l x2))  
  | p0l pplusl ptimesl pnegl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB p0l pplusl ptimesl pnegl p1l x1) (inductionB p0l pplusl ptimesl pnegl p1l x2))  
  | p0l pplusl ptimesl pnegl p1l (negL x1) := (pnegl _ (inductionB p0l pplusl ptimesl pnegl p1l x1))  
  | p0l pplusl ptimesl pnegl p1l oneL := p1l  
  def inductionCl   {A : Type} {P : ((ClLieRingTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClLieRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClLieRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 : (ClLieRingTerm A)) , ((P x1) → (P (negCl x1)))) → ((P oneCl) → (∀ (x : (ClLieRingTerm A)) , (P x)))))))) 
  | psing p0cl ppluscl ptimescl pnegcl p1cl (sing x1) := (psing x1)  
  | psing p0cl ppluscl ptimescl pnegcl p1cl zeroCl := p0cl  
  | psing p0cl ppluscl ptimescl pnegcl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl ptimescl pnegcl p1cl x1) (inductionCl psing p0cl ppluscl ptimescl pnegcl p1cl x2))  
  | psing p0cl ppluscl ptimescl pnegcl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ppluscl ptimescl pnegcl p1cl x1) (inductionCl psing p0cl ppluscl ptimescl pnegcl p1cl x2))  
  | psing p0cl ppluscl ptimescl pnegcl p1cl (negCl x1) := (pnegcl _ (inductionCl psing p0cl ppluscl ptimescl pnegcl p1cl x1))  
  | psing p0cl ppluscl ptimescl pnegcl p1cl oneCl := p1cl  
  def inductionOpB   {n : ℕ} {P : ((OpLieRingTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpLieRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpLieRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 : (OpLieRingTerm n)) , ((P x1) → (P (negOL x1)))) → ((P oneOL) → (∀ (x : (OpLieRingTerm n)) , (P x)))))))) 
  | pv p0ol pplusol ptimesol pnegol p1ol (v x1) := (pv x1)  
  | pv p0ol pplusol ptimesol pnegol p1ol zeroOL := p0ol  
  | pv p0ol pplusol ptimesol pnegol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol ptimesol pnegol p1ol x1) (inductionOpB pv p0ol pplusol ptimesol pnegol p1ol x2))  
  | pv p0ol pplusol ptimesol pnegol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol pplusol ptimesol pnegol p1ol x1) (inductionOpB pv p0ol pplusol ptimesol pnegol p1ol x2))  
  | pv p0ol pplusol ptimesol pnegol p1ol (negOL x1) := (pnegol _ (inductionOpB pv p0ol pplusol ptimesol pnegol p1ol x1))  
  | pv p0ol pplusol ptimesol pnegol p1ol oneOL := p1ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLieRingTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpLieRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpLieRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 : (OpLieRingTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → ((P oneOL2) → (∀ (x : (OpLieRingTerm2 n A)) , (P x))))))))) 
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 x1))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 pnegol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (LieRingTerm → (Staged LieRingTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  | oneL := (Now oneL)  
  def stageCl   {A : Type}  : ((ClLieRingTerm A) → (Staged (ClLieRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  | oneCl := (Now oneCl)  
  def stageOpB   {n : ℕ}  : ((OpLieRingTerm n) → (Staged (OpLieRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  | oneOL := (Now oneOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLieRingTerm2 n A) → (Staged (OpLieRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (negT : ((Repr A) → (Repr A)))
       (oneT : (Repr A)) 
  
end LieRing