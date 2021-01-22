import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section IdempotentSemiring   
  structure IdempotentSemiring  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (zero : A)
       (times : (A → (A → A)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (one : A)
       (lunit_one : (∀ {x : A} , (times one x) = x))
       (runit_one : (∀ {x : A} , (times x one) = x))
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (leftZero_op_zero : (∀ {x : A} , (times zero x) = zero))
       (rightZero_op_zero : (∀ {x : A} , (times x zero) = zero))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x)) 
  
  open IdempotentSemiring
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (timesS : (AS → (AS → AS)))
       (oneS : AS) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (oneP : (Prod A A))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (lunit_1P : (∀ {xP : (Prod A A)} , (timesP oneP xP) = xP))
       (runit_1P : (∀ {xP : (Prod A A)} , (timesP xP oneP) = xP))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (leftZero_op_0P : (∀ {xP : (Prod A A)} , (timesP zeroP xP) = zeroP))
       (rightZero_op_0P : (∀ {xP : (Prod A A)} , (timesP xP zeroP) = zeroP))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Id1 : (IdempotentSemiring A1)) (Id2 : (IdempotentSemiring A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Id1) x1 x2)) = ((plus Id2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Id1)) = (zero Id2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Id1) x1 x2)) = ((times Id2) (hom x1) (hom x2))))
       (pres_one : (hom (one Id1)) = (one Id2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Id1 : (IdempotentSemiring A1)) (Id2 : (IdempotentSemiring A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Id1) x1 x2) ((plus Id2) y1 y2))))))
       (interp_zero : (interp (zero Id1) (zero Id2)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Id1) x1 x2) ((times Id2) y1 y2))))))
       (interp_one : (interp (one Id1) (one Id2))) 
  
  inductive IdempotentSemiringTerm   : Type  
     | plusL : (IdempotentSemiringTerm → (IdempotentSemiringTerm → IdempotentSemiringTerm)) 
     | zeroL : IdempotentSemiringTerm 
     | timesL : (IdempotentSemiringTerm → (IdempotentSemiringTerm → IdempotentSemiringTerm)) 
     | oneL : IdempotentSemiringTerm  
      open IdempotentSemiringTerm 
  
  inductive ClIdempotentSemiringTerm  (A : Type) : Type  
     | sing : (A → ClIdempotentSemiringTerm) 
     | plusCl : (ClIdempotentSemiringTerm → (ClIdempotentSemiringTerm → ClIdempotentSemiringTerm)) 
     | zeroCl : ClIdempotentSemiringTerm 
     | timesCl : (ClIdempotentSemiringTerm → (ClIdempotentSemiringTerm → ClIdempotentSemiringTerm)) 
     | oneCl : ClIdempotentSemiringTerm  
      open ClIdempotentSemiringTerm 
  
  inductive OpIdempotentSemiringTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpIdempotentSemiringTerm) 
     | plusOL : (OpIdempotentSemiringTerm → (OpIdempotentSemiringTerm → OpIdempotentSemiringTerm)) 
     | zeroOL : OpIdempotentSemiringTerm 
     | timesOL : (OpIdempotentSemiringTerm → (OpIdempotentSemiringTerm → OpIdempotentSemiringTerm)) 
     | oneOL : OpIdempotentSemiringTerm  
      open OpIdempotentSemiringTerm 
  
  inductive OpIdempotentSemiringTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpIdempotentSemiringTerm2) 
     | sing2 : (A → OpIdempotentSemiringTerm2) 
     | plusOL2 : (OpIdempotentSemiringTerm2 → (OpIdempotentSemiringTerm2 → OpIdempotentSemiringTerm2)) 
     | zeroOL2 : OpIdempotentSemiringTerm2 
     | timesOL2 : (OpIdempotentSemiringTerm2 → (OpIdempotentSemiringTerm2 → OpIdempotentSemiringTerm2)) 
     | oneOL2 : OpIdempotentSemiringTerm2  
      open OpIdempotentSemiringTerm2 
  
  def simplifyCl   {A : Type}  : ((ClIdempotentSemiringTerm A) → (ClIdempotentSemiringTerm A)) 
  | (timesCl oneCl x) := x  
  | (timesCl x oneCl) := x  
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | oneCl := oneCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpIdempotentSemiringTerm n) → (OpIdempotentSemiringTerm n)) 
  | (timesOL oneOL x) := x  
  | (timesOL x oneOL) := x  
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | oneOL := oneOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpIdempotentSemiringTerm2 n A) → (OpIdempotentSemiringTerm2 n A)) 
  | (timesOL2 oneOL2 x) := x  
  | (timesOL2 x oneOL2) := x  
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | oneOL2 := oneOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((IdempotentSemiring A) → (IdempotentSemiringTerm → A)) 
  | Id (plusL x1 x2) := ((plus Id) (evalB Id x1) (evalB Id x2))  
  | Id zeroL := (zero Id)  
  | Id (timesL x1 x2) := ((times Id) (evalB Id x1) (evalB Id x2))  
  | Id oneL := (one Id)  
  def evalCl   {A : Type}  : ((IdempotentSemiring A) → ((ClIdempotentSemiringTerm A) → A)) 
  | Id (sing x1) := x1  
  | Id (plusCl x1 x2) := ((plus Id) (evalCl Id x1) (evalCl Id x2))  
  | Id zeroCl := (zero Id)  
  | Id (timesCl x1 x2) := ((times Id) (evalCl Id x1) (evalCl Id x2))  
  | Id oneCl := (one Id)  
  def evalOpB   {A : Type} {n : ℕ}  : ((IdempotentSemiring A) → ((vector A n) → ((OpIdempotentSemiringTerm n) → A))) 
  | Id vars (v x1) := (nth vars x1)  
  | Id vars (plusOL x1 x2) := ((plus Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  | Id vars zeroOL := (zero Id)  
  | Id vars (timesOL x1 x2) := ((times Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  | Id vars oneOL := (one Id)  
  def evalOp   {A : Type} {n : ℕ}  : ((IdempotentSemiring A) → ((vector A n) → ((OpIdempotentSemiringTerm2 n A) → A))) 
  | Id vars (v2 x1) := (nth vars x1)  
  | Id vars (sing2 x1) := x1  
  | Id vars (plusOL2 x1 x2) := ((plus Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  | Id vars zeroOL2 := (zero Id)  
  | Id vars (timesOL2 x1 x2) := ((times Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  | Id vars oneOL2 := (one Id)  
  def inductionB   {P : (IdempotentSemiringTerm → Type)}  : ((∀ (x1 x2 : IdempotentSemiringTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 x2 : IdempotentSemiringTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P oneL) → (∀ (x : IdempotentSemiringTerm) , (P x)))))) 
  | pplusl p0l ptimesl p1l (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l ptimesl p1l x1) (inductionB pplusl p0l ptimesl p1l x2))  
  | pplusl p0l ptimesl p1l zeroL := p0l  
  | pplusl p0l ptimesl p1l (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl p0l ptimesl p1l x1) (inductionB pplusl p0l ptimesl p1l x2))  
  | pplusl p0l ptimesl p1l oneL := p1l  
  def inductionCl   {A : Type} {P : ((ClIdempotentSemiringTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClIdempotentSemiringTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 x2 : (ClIdempotentSemiringTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P oneCl) → (∀ (x : (ClIdempotentSemiringTerm A)) , (P x))))))) 
  | psing ppluscl p0cl ptimescl p1cl (sing x1) := (psing x1)  
  | psing ppluscl p0cl ptimescl p1cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl ptimescl p1cl x1) (inductionCl psing ppluscl p0cl ptimescl p1cl x2))  
  | psing ppluscl p0cl ptimescl p1cl zeroCl := p0cl  
  | psing ppluscl p0cl ptimescl p1cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl p0cl ptimescl p1cl x1) (inductionCl psing ppluscl p0cl ptimescl p1cl x2))  
  | psing ppluscl p0cl ptimescl p1cl oneCl := p1cl  
  def inductionOpB   {n : ℕ} {P : ((OpIdempotentSemiringTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpIdempotentSemiringTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 x2 : (OpIdempotentSemiringTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P oneOL) → (∀ (x : (OpIdempotentSemiringTerm n)) , (P x))))))) 
  | pv pplusol p0ol ptimesol p1ol (v x1) := (pv x1)  
  | pv pplusol p0ol ptimesol p1ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol ptimesol p1ol x1) (inductionOpB pv pplusol p0ol ptimesol p1ol x2))  
  | pv pplusol p0ol ptimesol p1ol zeroOL := p0ol  
  | pv pplusol p0ol ptimesol p1ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol p0ol ptimesol p1ol x1) (inductionOpB pv pplusol p0ol ptimesol p1ol x2))  
  | pv pplusol p0ol ptimesol p1ol oneOL := p1ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpIdempotentSemiringTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpIdempotentSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpIdempotentSemiringTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P oneOL2) → (∀ (x : (OpIdempotentSemiringTerm2 n A)) , (P x)))))))) 
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 zeroOL2 := p0ol2  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 ptimesol2 p1ol2 oneOL2 := p1ol2  
  def stageB  : (IdempotentSemiringTerm → (Staged IdempotentSemiringTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | oneL := (Now oneL)  
  def stageCl   {A : Type}  : ((ClIdempotentSemiringTerm A) → (Staged (ClIdempotentSemiringTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | oneCl := (Now oneCl)  
  def stageOpB   {n : ℕ}  : ((OpIdempotentSemiringTerm n) → (Staged (OpIdempotentSemiringTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | oneOL := (Now oneOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpIdempotentSemiringTerm2 n A) → (Staged (OpIdempotentSemiringTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | oneOL2 := (Now oneOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (oneT : (Repr A)) 
  
end IdempotentSemiring