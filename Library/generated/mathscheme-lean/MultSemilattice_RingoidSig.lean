import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section MultSemilattice_RingoidSig   
  structure MultSemilattice_RingoidSig  (A : Type) : Type := 
       (times : (A → (A → A)))
       (commutative_times : (∀ {x y : A} , (times x y) = (times y x)))
       (associative_times : (∀ {x y z : A} , (times (times x y) z) = (times x (times y z))))
       (idempotent_times : (∀ {x : A} , (times x x) = x))
       (plus : (A → (A → A))) 
  
  open MultSemilattice_RingoidSig
  structure Sig  (AS : Type) : Type := 
       (timesS : (AS → (AS → AS)))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_timesP : (∀ {xP yP : (Prod A A)} , (timesP xP yP) = (timesP yP xP)))
       (associative_timesP : (∀ {xP yP zP : (Prod A A)} , (timesP (timesP xP yP) zP) = (timesP xP (timesP yP zP))))
       (idempotent_timesP : (∀ {xP : (Prod A A)} , (timesP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Mu1 : (MultSemilattice_RingoidSig A1)) (Mu2 : (MultSemilattice_RingoidSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Mu1) x1 x2)) = ((times Mu2) (hom x1) (hom x2))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Mu1) x1 x2)) = ((plus Mu2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Mu1 : (MultSemilattice_RingoidSig A1)) (Mu2 : (MultSemilattice_RingoidSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Mu1) x1 x2) ((times Mu2) y1 y2))))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Mu1) x1 x2) ((plus Mu2) y1 y2)))))) 
  
  inductive MultSemilattice_RingoidSigTerm   : Type  
     | timesL : (MultSemilattice_RingoidSigTerm → (MultSemilattice_RingoidSigTerm → MultSemilattice_RingoidSigTerm)) 
     | plusL : (MultSemilattice_RingoidSigTerm → (MultSemilattice_RingoidSigTerm → MultSemilattice_RingoidSigTerm))  
      open MultSemilattice_RingoidSigTerm 
  
  inductive ClMultSemilattice_RingoidSigTerm  (A : Type) : Type  
     | sing : (A → ClMultSemilattice_RingoidSigTerm) 
     | timesCl : (ClMultSemilattice_RingoidSigTerm → (ClMultSemilattice_RingoidSigTerm → ClMultSemilattice_RingoidSigTerm)) 
     | plusCl : (ClMultSemilattice_RingoidSigTerm → (ClMultSemilattice_RingoidSigTerm → ClMultSemilattice_RingoidSigTerm))  
      open ClMultSemilattice_RingoidSigTerm 
  
  inductive OpMultSemilattice_RingoidSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpMultSemilattice_RingoidSigTerm) 
     | timesOL : (OpMultSemilattice_RingoidSigTerm → (OpMultSemilattice_RingoidSigTerm → OpMultSemilattice_RingoidSigTerm)) 
     | plusOL : (OpMultSemilattice_RingoidSigTerm → (OpMultSemilattice_RingoidSigTerm → OpMultSemilattice_RingoidSigTerm))  
      open OpMultSemilattice_RingoidSigTerm 
  
  inductive OpMultSemilattice_RingoidSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpMultSemilattice_RingoidSigTerm2) 
     | sing2 : (A → OpMultSemilattice_RingoidSigTerm2) 
     | timesOL2 : (OpMultSemilattice_RingoidSigTerm2 → (OpMultSemilattice_RingoidSigTerm2 → OpMultSemilattice_RingoidSigTerm2)) 
     | plusOL2 : (OpMultSemilattice_RingoidSigTerm2 → (OpMultSemilattice_RingoidSigTerm2 → OpMultSemilattice_RingoidSigTerm2))  
      open OpMultSemilattice_RingoidSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClMultSemilattice_RingoidSigTerm A) → (ClMultSemilattice_RingoidSigTerm A)) 
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpMultSemilattice_RingoidSigTerm n) → (OpMultSemilattice_RingoidSigTerm n)) 
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpMultSemilattice_RingoidSigTerm2 n A) → (OpMultSemilattice_RingoidSigTerm2 n A)) 
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((MultSemilattice_RingoidSig A) → (MultSemilattice_RingoidSigTerm → A)) 
  | Mu (timesL x1 x2) := ((times Mu) (evalB Mu x1) (evalB Mu x2))  
  | Mu (plusL x1 x2) := ((plus Mu) (evalB Mu x1) (evalB Mu x2))  
  def evalCl   {A : Type}  : ((MultSemilattice_RingoidSig A) → ((ClMultSemilattice_RingoidSigTerm A) → A)) 
  | Mu (sing x1) := x1  
  | Mu (timesCl x1 x2) := ((times Mu) (evalCl Mu x1) (evalCl Mu x2))  
  | Mu (plusCl x1 x2) := ((plus Mu) (evalCl Mu x1) (evalCl Mu x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((MultSemilattice_RingoidSig A) → ((vector A n) → ((OpMultSemilattice_RingoidSigTerm n) → A))) 
  | Mu vars (v x1) := (nth vars x1)  
  | Mu vars (timesOL x1 x2) := ((times Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  | Mu vars (plusOL x1 x2) := ((plus Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((MultSemilattice_RingoidSig A) → ((vector A n) → ((OpMultSemilattice_RingoidSigTerm2 n A) → A))) 
  | Mu vars (v2 x1) := (nth vars x1)  
  | Mu vars (sing2 x1) := x1  
  | Mu vars (timesOL2 x1 x2) := ((times Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  | Mu vars (plusOL2 x1 x2) := ((plus Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  def inductionB   {P : (MultSemilattice_RingoidSigTerm → Type)}  : ((∀ (x1 x2 : MultSemilattice_RingoidSigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → ((∀ (x1 x2 : MultSemilattice_RingoidSigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : MultSemilattice_RingoidSigTerm) , (P x)))) 
  | ptimesl pplusl (timesL x1 x2) := (ptimesl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  | ptimesl pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ptimesl pplusl x1) (inductionB ptimesl pplusl x2))  
  def inductionCl   {A : Type} {P : ((ClMultSemilattice_RingoidSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClMultSemilattice_RingoidSigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → ((∀ (x1 x2 : (ClMultSemilattice_RingoidSigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClMultSemilattice_RingoidSigTerm A)) , (P x))))) 
  | psing ptimescl ppluscl (sing x1) := (psing x1)  
  | psing ptimescl ppluscl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  | psing ptimescl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ptimescl ppluscl x1) (inductionCl psing ptimescl ppluscl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpMultSemilattice_RingoidSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpMultSemilattice_RingoidSigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → ((∀ (x1 x2 : (OpMultSemilattice_RingoidSigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpMultSemilattice_RingoidSigTerm n)) , (P x))))) 
  | pv ptimesol pplusol (v x1) := (pv x1)  
  | pv ptimesol pplusol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  | pv ptimesol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv ptimesol pplusol x1) (inductionOpB pv ptimesol pplusol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpMultSemilattice_RingoidSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpMultSemilattice_RingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → ((∀ (x1 x2 : (OpMultSemilattice_RingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpMultSemilattice_RingoidSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 ptimesol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 ptimesol2 pplusol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  | pv2 psing2 ptimesol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 ptimesol2 pplusol2 x1) (inductionOp pv2 psing2 ptimesol2 pplusol2 x2))  
  def stageB  : (MultSemilattice_RingoidSigTerm → (Staged MultSemilattice_RingoidSigTerm))
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClMultSemilattice_RingoidSigTerm A) → (Staged (ClMultSemilattice_RingoidSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpMultSemilattice_RingoidSigTerm n) → (Staged (OpMultSemilattice_RingoidSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpMultSemilattice_RingoidSigTerm2 n A) → (Staged (OpMultSemilattice_RingoidSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (timesT : ((Repr A) → ((Repr A) → (Repr A))))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end MultSemilattice_RingoidSig