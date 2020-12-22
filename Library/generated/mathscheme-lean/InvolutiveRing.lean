import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section InvolutiveRing   
  structure InvolutiveRing  (A : Type) : Type := 
       (times : (A → (A → A)))
       (plus : (A → (A → A)))
       (one : A)
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (prim : (A → A))
       (fixes_prim_one : (prim one) = one)
       (involutive_prim : (∀ {x : A} , (prim (prim x)) = x))
       (antidis_prim_plus : (∀ {x y : A} , (prim (plus x y)) = (plus (prim y) (prim x))))
       (antidis_prim_times : (∀ {x y : A} , (prim (times x y)) = (times (prim y) (prim x))))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero))
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero)) 
  
  open InvolutiveRing
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS)))
       (oneS : AS)
       (primS : (AS → AS))
       (zeroS : AS)
       (negS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (primP : ((Prod A A) → (Prod A A)))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (fixes_prim_1P : (primP oneP) = oneP)
       (involutive_primP : (∀ {xP : (Prod A A)} , (primP (primP xP)) = xP))
       (antidis_prim_plusP : (∀ {xP yP : (Prod A A)} , (primP (plusP xP yP)) = (plusP (primP yP) (primP xP))))
       (antidis_prim_timesP : (∀ {xP yP : (Prod A A)} , (primP (timesP xP yP)) = (timesP (primP yP) (primP xP))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRing A1)) (In2 : (InvolutiveRing A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times In1) x1 x2)) = ((times In2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus In1) x1 x2)) = ((plus In2) (hom x1) (hom x2))))
       (pres_one : (hom (one In1)) = (one In2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim In1) x1)) = ((prim In2) (hom x1))))
       (pres_zero : (hom (zero In1)) = (zero In2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg In1) x1)) = ((neg In2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (In1 : (InvolutiveRing A1)) (In2 : (InvolutiveRing A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times In1) x1 x2) ((times In2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus In1) x1 x2) ((plus In2) y1 y2))))))
       (interp_one : (interp (one In1) (one In2)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))))
       (interp_zero : (interp (zero In1) (zero In2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg In1) x1) ((neg In2) y1))))) 
  
  inductive InvolutiveRingTerm   : Type  
     | timesL : (InvolutiveRingTerm → (InvolutiveRingTerm → InvolutiveRingTerm)) 
     | plusL : (InvolutiveRingTerm → (InvolutiveRingTerm → InvolutiveRingTerm)) 
     | oneL : InvolutiveRingTerm 
     | primL : (InvolutiveRingTerm → InvolutiveRingTerm) 
     | zeroL : InvolutiveRingTerm 
     | negL : (InvolutiveRingTerm → InvolutiveRingTerm)  
      open InvolutiveRingTerm 
  
  inductive ClInvolutiveRingTerm  (A : Type) : Type  
     | sing : (A → ClInvolutiveRingTerm) 
     | timesCl : (ClInvolutiveRingTerm → (ClInvolutiveRingTerm → ClInvolutiveRingTerm)) 
     | plusCl : (ClInvolutiveRingTerm → (ClInvolutiveRingTerm → ClInvolutiveRingTerm)) 
     | oneCl : ClInvolutiveRingTerm 
     | primCl : (ClInvolutiveRingTerm → ClInvolutiveRingTerm) 
     | zeroCl : ClInvolutiveRingTerm 
     | negCl : (ClInvolutiveRingTerm → ClInvolutiveRingTerm)  
      open ClInvolutiveRingTerm 
  
  inductive OpInvolutiveRingTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpInvolutiveRingTerm) 
     | timesOL : (OpInvolutiveRingTerm → (OpInvolutiveRingTerm → OpInvolutiveRingTerm)) 
     | plusOL : (OpInvolutiveRingTerm → (OpInvolutiveRingTerm → OpInvolutiveRingTerm)) 
     | oneOL : OpInvolutiveRingTerm 
     | primOL : (OpInvolutiveRingTerm → OpInvolutiveRingTerm) 
     | zeroOL : OpInvolutiveRingTerm 
     | negOL : (OpInvolutiveRingTerm → OpInvolutiveRingTerm)  
      open OpInvolutiveRingTerm 
  
  inductive OpInvolutiveRingTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpInvolutiveRingTerm2) 
     | sing2 : (A → OpInvolutiveRingTerm2) 
     | timesOL2 : (OpInvolutiveRingTerm2 → (OpInvolutiveRingTerm2 → OpInvolutiveRingTerm2)) 
     | plusOL2 : (OpInvolutiveRingTerm2 → (OpInvolutiveRingTerm2 → OpInvolutiveRingTerm2)) 
     | oneOL2 : OpInvolutiveRingTerm2 
     | primOL2 : (OpInvolutiveRingTerm2 → OpInvolutiveRingTerm2) 
     | zeroOL2 : OpInvolutiveRingTerm2 
     | negOL2 : (OpInvolutiveRingTerm2 → OpInvolutiveRingTerm2)  
      open OpInvolutiveRingTerm2 
  
  def simplifyCl   (A : Type)  : ((ClInvolutiveRingTerm A) → (ClInvolutiveRingTerm A)) 
  | (primCl oneCl) := oneCl  
  | (primCl (primCl x)) := x  
  | (plusCl (primCl y) (primCl x)) := (primCl (plusCl x y))  
  | (timesCl (primCl y) (primCl x)) := (primCl (timesCl x y))  
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpInvolutiveRingTerm n) → (OpInvolutiveRingTerm n)) 
  | (primOL oneOL) := oneOL  
  | (primOL (primOL x)) := x  
  | (plusOL (primOL y) (primOL x)) := (primOL (plusOL x y))  
  | (timesOL (primOL y) (primOL x)) := (primOL (timesOL x y))  
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpInvolutiveRingTerm2 n A) → (OpInvolutiveRingTerm2 n A)) 
  | (primOL2 oneOL2) := oneOL2  
  | (primOL2 (primOL2 x)) := x  
  | (plusOL2 (primOL2 y) (primOL2 x)) := (primOL2 (plusOL2 x y))  
  | (timesOL2 (primOL2 y) (primOL2 x)) := (primOL2 (timesOL2 x y))  
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((InvolutiveRing A) → (InvolutiveRingTerm → A)) 
  | In (timesL x1 x2) := ((times In) (evalB In x1) (evalB In x2))  
  | In (plusL x1 x2) := ((plus In) (evalB In x1) (evalB In x2))  
  | In oneL := (one In)  
  | In (primL x1) := ((prim In) (evalB In x1))  
  | In zeroL := (zero In)  
  | In (negL x1) := ((neg In) (evalB In x1))  
  def evalCl   {A : Type}  : ((InvolutiveRing A) → ((ClInvolutiveRingTerm A) → A)) 
  | In (sing x1) := x1  
  | In (timesCl x1 x2) := ((times In) (evalCl In x1) (evalCl In x2))  
  | In (plusCl x1 x2) := ((plus In) (evalCl In x1) (evalCl In x2))  
  | In oneCl := (one In)  
  | In (primCl x1) := ((prim In) (evalCl In x1))  
  | In zeroCl := (zero In)  
  | In (negCl x1) := ((neg In) (evalCl In x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((InvolutiveRing A) → ((vector A n) → ((OpInvolutiveRingTerm n) → A))) 
  | In vars (v x1) := (nth vars x1)  
  | In vars (timesOL x1 x2) := ((times In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars (plusOL x1 x2) := ((plus In) (evalOpB In vars x1) (evalOpB In vars x2))  
  | In vars oneOL := (one In)  
  | In vars (primOL x1) := ((prim In) (evalOpB In vars x1))  
  | In vars zeroOL := (zero In)  
  | In vars (negOL x1) := ((neg In) (evalOpB In vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((InvolutiveRing A) → ((vector A n) → ((OpInvolutiveRingTerm2 n A) → A))) 
  | In vars (v2 x1) := (nth vars x1)  
  | In vars (sing2 x1) := x1  
  | In vars (timesOL2 x1 x2) := ((times In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars (plusOL2 x1 x2) := ((plus In) (evalOp In vars x1) (evalOp In vars x2))  
  | In vars oneOL2 := (one In)  
  | In vars (primOL2 x1) := ((prim In) (evalOp In vars x1))  
  | In vars zeroOL2 := (zero In)  
  | In vars (negOL2 x1) := ((neg In) (evalOp In vars x1))  
  def inductionB   (P : (InvolutiveRingTerm → Type))  : ((∀ (x1 x2 : InvolutiveRingTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : InvolutiveRingTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P oneL) → ((∀ (x1 : InvolutiveRingTerm) , ((P x1) → (P (primL x1)))) → ((P zeroL) → ((∀ (x1 : InvolutiveRingTerm) , ((P x1) → (P (negL x1)))) → (∀ (x : InvolutiveRingTerm) , (P x)))))))) 
  | ptimesl pplusl p1l ppriml p0l pnegl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl p1l ppriml p0l pnegl x1) (inductionB ptimesl pplusl p1l ppriml p0l pnegl x2))  
  | ptimesl pplusl p1l ppriml p0l pnegl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl p1l ppriml p0l pnegl x1) (inductionB ptimesl pplusl p1l ppriml p0l pnegl x2))  
  | ptimesl pplusl p1l ppriml p0l pnegl oneL := p1l  
  | ptimesl pplusl p1l ppriml p0l pnegl (primL x1) := (ppriml _ (inductionB ptimesl pplusl p1l ppriml p0l pnegl x1))  
  | ptimesl pplusl p1l ppriml p0l pnegl zeroL := p0l  
  | ptimesl pplusl p1l ppriml p0l pnegl (negL x1) := (pnegl _ (inductionB ptimesl pplusl p1l ppriml p0l pnegl x1))  
  def inductionCl   (A : Type) (P : ((ClInvolutiveRingTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClInvolutiveRingTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClInvolutiveRingTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P oneCl) → ((∀ (x1 : (ClInvolutiveRingTerm A)) , ((P x1) → (P (primCl x1)))) → ((P zeroCl) → ((∀ (x1 : (ClInvolutiveRingTerm A)) , ((P x1) → (P (negCl x1)))) → (∀ (x : (ClInvolutiveRingTerm A)) , (P x))))))))) 
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl x1) (inductionCl psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl x2))  
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl x1) (inductionCl psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl x2))  
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl oneCl := p1cl  
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl (primCl x1) := (pprimcl _ (inductionCl psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl x1))  
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl zeroCl := p0cl  
  | psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl (negCl x1) := (pnegcl _ (inductionCl psing ptimescl ppluscl p1cl pprimcl p0cl pnegcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpInvolutiveRingTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpInvolutiveRingTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P oneOL) → ((∀ (x1 : (OpInvolutiveRingTerm n)) , ((P x1) → (P (primOL x1)))) → ((P zeroOL) → ((∀ (x1 : (OpInvolutiveRingTerm n)) , ((P x1) → (P (negOL x1)))) → (∀ (x : (OpInvolutiveRingTerm n)) , (P x))))))))) 
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol (v x1) := (pv x1)  
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol p1ol pprimol p0ol pnegol x1) (inductionOpB pv ptimesol pplusol p1ol pprimol p0ol pnegol x2))  
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol p1ol pprimol p0ol pnegol x1) (inductionOpB pv ptimesol pplusol p1ol pprimol p0ol pnegol x2))  
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol oneOL := p1ol  
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol (primOL x1) := (pprimol _ (inductionOpB pv ptimesol pplusol p1ol pprimol p0ol pnegol x1))  
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol zeroOL := p0ol  
  | pv ptimesol pplusol p1ol pprimol p0ol pnegol (negOL x1) := (pnegol _ (inductionOpB pv ptimesol pplusol p1ol pprimol p0ol pnegol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpInvolutiveRingTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpInvolutiveRingTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpInvolutiveRingTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P oneOL2) → ((∀ (x1 : (OpInvolutiveRingTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((P zeroOL2) → ((∀ (x1 : (OpInvolutiveRingTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → (∀ (x : (OpInvolutiveRingTerm2 n A)) , (P x)))))))))) 
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 oneOL2 := p1ol2  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 x1))  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 zeroOL2 := p0ol2  
  | pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 ptimesol2 pplusol2 p1ol2 pprimol2 p0ol2 pnegol2 x1))  
  def stageB  : (InvolutiveRingTerm → (Staged InvolutiveRingTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClInvolutiveRingTerm A) → (Staged (ClInvolutiveRingTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpInvolutiveRingTerm n) → (Staged (OpInvolutiveRingTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpInvolutiveRingTerm2 n A) → (Staged (OpInvolutiveRingTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A))
       (primT : ((Repr A) → (Repr A)))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A))) 
  
end InvolutiveRing