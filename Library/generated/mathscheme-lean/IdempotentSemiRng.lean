import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section IdempotentSemiRng   
  structure IdempotentSemiRng  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (times : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (leftDistributive_times_plus : (∀ {x y z : A} , (times x (plus y z)) = (plus (times x y) (times x z))))
       (rightDistributive_times_plus : (∀ {x y z : A} , (times (plus y z) x) = (plus (times y x) (times z x))))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x)) 
  
  open IdempotentSemiRng
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS)))
       (zeroS : AS) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (leftDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP xP (plusP yP zP)) = (plusP (timesP xP yP) (timesP xP zP))))
       (rightDistributive_times_plusP : (∀ {xP yP zP : (Prod A A)} , (timesP (plusP yP zP) xP) = (plusP (timesP yP xP) (timesP zP xP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Id1 : (IdempotentSemiRng A1)) (Id2 : (IdempotentSemiRng A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Id1) x1 x2)) = ((plus Id2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Id1) x1 x2)) = ((times Id2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Id1)) = (zero Id2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Id1 : (IdempotentSemiRng A1)) (Id2 : (IdempotentSemiRng A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Id1) x1 x2) ((plus Id2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Id1) x1 x2) ((times Id2) y1 y2))))))
       (interp_zero : (interp (zero Id1) (zero Id2))) 
  
  inductive IdempotentSemiRngTerm   : Type  
     | plusL : (IdempotentSemiRngTerm → (IdempotentSemiRngTerm → IdempotentSemiRngTerm)) 
     | timesL : (IdempotentSemiRngTerm → (IdempotentSemiRngTerm → IdempotentSemiRngTerm)) 
     | zeroL : IdempotentSemiRngTerm  
      open IdempotentSemiRngTerm 
  
  inductive ClIdempotentSemiRngTerm  (A : Type) : Type  
     | sing : (A → ClIdempotentSemiRngTerm) 
     | plusCl : (ClIdempotentSemiRngTerm → (ClIdempotentSemiRngTerm → ClIdempotentSemiRngTerm)) 
     | timesCl : (ClIdempotentSemiRngTerm → (ClIdempotentSemiRngTerm → ClIdempotentSemiRngTerm)) 
     | zeroCl : ClIdempotentSemiRngTerm  
      open ClIdempotentSemiRngTerm 
  
  inductive OpIdempotentSemiRngTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpIdempotentSemiRngTerm) 
     | plusOL : (OpIdempotentSemiRngTerm → (OpIdempotentSemiRngTerm → OpIdempotentSemiRngTerm)) 
     | timesOL : (OpIdempotentSemiRngTerm → (OpIdempotentSemiRngTerm → OpIdempotentSemiRngTerm)) 
     | zeroOL : OpIdempotentSemiRngTerm  
      open OpIdempotentSemiRngTerm 
  
  inductive OpIdempotentSemiRngTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpIdempotentSemiRngTerm2) 
     | sing2 : (A → OpIdempotentSemiRngTerm2) 
     | plusOL2 : (OpIdempotentSemiRngTerm2 → (OpIdempotentSemiRngTerm2 → OpIdempotentSemiRngTerm2)) 
     | timesOL2 : (OpIdempotentSemiRngTerm2 → (OpIdempotentSemiRngTerm2 → OpIdempotentSemiRngTerm2)) 
     | zeroOL2 : OpIdempotentSemiRngTerm2  
      open OpIdempotentSemiRngTerm2 
  
  def simplifyCl   {A : Type}  : ((ClIdempotentSemiRngTerm A) → (ClIdempotentSemiRngTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpIdempotentSemiRngTerm n) → (OpIdempotentSemiRngTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpIdempotentSemiRngTerm2 n A) → (OpIdempotentSemiRngTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((IdempotentSemiRng A) → (IdempotentSemiRngTerm → A)) 
  | Id (plusL x1 x2) := ((plus Id) (evalB Id x1) (evalB Id x2))  
  | Id (timesL x1 x2) := ((times Id) (evalB Id x1) (evalB Id x2))  
  | Id zeroL := (zero Id)  
  def evalCl   {A : Type}  : ((IdempotentSemiRng A) → ((ClIdempotentSemiRngTerm A) → A)) 
  | Id (sing x1) := x1  
  | Id (plusCl x1 x2) := ((plus Id) (evalCl Id x1) (evalCl Id x2))  
  | Id (timesCl x1 x2) := ((times Id) (evalCl Id x1) (evalCl Id x2))  
  | Id zeroCl := (zero Id)  
  def evalOpB   {A : Type} {n : ℕ}  : ((IdempotentSemiRng A) → ((vector A n) → ((OpIdempotentSemiRngTerm n) → A))) 
  | Id vars (v x1) := (nth vars x1)  
  | Id vars (plusOL x1 x2) := ((plus Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  | Id vars (timesOL x1 x2) := ((times Id) (evalOpB Id vars x1) (evalOpB Id vars x2))  
  | Id vars zeroOL := (zero Id)  
  def evalOp   {A : Type} {n : ℕ}  : ((IdempotentSemiRng A) → ((vector A n) → ((OpIdempotentSemiRngTerm2 n A) → A))) 
  | Id vars (v2 x1) := (nth vars x1)  
  | Id vars (sing2 x1) := x1  
  | Id vars (plusOL2 x1 x2) := ((plus Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  | Id vars (timesOL2 x1 x2) := ((times Id) (evalOp Id vars x1) (evalOp Id vars x2))  
  | Id vars zeroOL2 := (zero Id)  
  def inductionB   {P : (IdempotentSemiRngTerm → Type)}  : ((∀ (x1 x2 : IdempotentSemiRngTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : IdempotentSemiRngTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((P zeroL) → (∀ (x : IdempotentSemiRngTerm) , (P x))))) 
  | pplusl ptimesl p0l (plusL x1 x2) := (pplusl _ _ (inductionB pplusl ptimesl p0l x1) (inductionB pplusl ptimesl p0l x2))  
  | pplusl ptimesl p0l (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl ptimesl p0l x1) (inductionB pplusl ptimesl p0l x2))  
  | pplusl ptimesl p0l zeroL := p0l  
  def inductionCl   {A : Type} {P : ((ClIdempotentSemiRngTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClIdempotentSemiRngTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClIdempotentSemiRngTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((P zeroCl) → (∀ (x : (ClIdempotentSemiRngTerm A)) , (P x)))))) 
  | psing ppluscl ptimescl p0cl (sing x1) := (psing x1)  
  | psing ppluscl ptimescl p0cl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl ptimescl p0cl x1) (inductionCl psing ppluscl ptimescl p0cl x2))  
  | psing ppluscl ptimescl p0cl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl ptimescl p0cl x1) (inductionCl psing ppluscl ptimescl p0cl x2))  
  | psing ppluscl ptimescl p0cl zeroCl := p0cl  
  def inductionOpB   {n : ℕ} {P : ((OpIdempotentSemiRngTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpIdempotentSemiRngTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpIdempotentSemiRngTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((P zeroOL) → (∀ (x : (OpIdempotentSemiRngTerm n)) , (P x)))))) 
  | pv pplusol ptimesol p0ol (v x1) := (pv x1)  
  | pv pplusol ptimesol p0ol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol ptimesol p0ol x1) (inductionOpB pv pplusol ptimesol p0ol x2))  
  | pv pplusol ptimesol p0ol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol ptimesol p0ol x1) (inductionOpB pv pplusol ptimesol p0ol x2))  
  | pv pplusol ptimesol p0ol zeroOL := p0ol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpIdempotentSemiRngTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpIdempotentSemiRngTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpIdempotentSemiRngTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((P zeroOL2) → (∀ (x : (OpIdempotentSemiRngTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pplusol2 ptimesol2 p0ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 p0ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 p0ol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 p0ol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 p0ol2 x2))  
  | pv2 psing2 pplusol2 ptimesol2 p0ol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 p0ol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 p0ol2 x2))  
  | pv2 psing2 pplusol2 ptimesol2 p0ol2 zeroOL2 := p0ol2  
  def stageB  : (IdempotentSemiRngTerm → (Staged IdempotentSemiRngTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  def stageCl   {A : Type}  : ((ClIdempotentSemiRngTerm A) → (Staged (ClIdempotentSemiRngTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  def stageOpB   {n : ℕ}  : ((OpIdempotentSemiRngTerm n) → (Staged (OpIdempotentSemiRngTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpIdempotentSemiRngTerm2 n A) → (Staged (OpIdempotentSemiRngTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A)) 
  
end IdempotentSemiRng