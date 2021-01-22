import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section JoinSemilattice_RingoidSig   
  structure JoinSemilattice_RingoidSig  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (idempotent_plus : (∀ {x : A} , (plus x x) = x))
       (times : (A → (A → A))) 
  
  open JoinSemilattice_RingoidSig
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (idempotent_plusP : (∀ {xP : (Prod A A)} , (plusP xP xP) = xP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Jo1 : (JoinSemilattice_RingoidSig A1)) (Jo2 : (JoinSemilattice_RingoidSig A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Jo1) x1 x2)) = ((plus Jo2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Jo1) x1 x2)) = ((times Jo2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Jo1 : (JoinSemilattice_RingoidSig A1)) (Jo2 : (JoinSemilattice_RingoidSig A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Jo1) x1 x2) ((plus Jo2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Jo1) x1 x2) ((times Jo2) y1 y2)))))) 
  
  inductive JoinSemilattice_RingoidSigTerm   : Type  
     | plusL : (JoinSemilattice_RingoidSigTerm → (JoinSemilattice_RingoidSigTerm → JoinSemilattice_RingoidSigTerm)) 
     | timesL : (JoinSemilattice_RingoidSigTerm → (JoinSemilattice_RingoidSigTerm → JoinSemilattice_RingoidSigTerm))  
      open JoinSemilattice_RingoidSigTerm 
  
  inductive ClJoinSemilattice_RingoidSigTerm  (A : Type) : Type  
     | sing : (A → ClJoinSemilattice_RingoidSigTerm) 
     | plusCl : (ClJoinSemilattice_RingoidSigTerm → (ClJoinSemilattice_RingoidSigTerm → ClJoinSemilattice_RingoidSigTerm)) 
     | timesCl : (ClJoinSemilattice_RingoidSigTerm → (ClJoinSemilattice_RingoidSigTerm → ClJoinSemilattice_RingoidSigTerm))  
      open ClJoinSemilattice_RingoidSigTerm 
  
  inductive OpJoinSemilattice_RingoidSigTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpJoinSemilattice_RingoidSigTerm) 
     | plusOL : (OpJoinSemilattice_RingoidSigTerm → (OpJoinSemilattice_RingoidSigTerm → OpJoinSemilattice_RingoidSigTerm)) 
     | timesOL : (OpJoinSemilattice_RingoidSigTerm → (OpJoinSemilattice_RingoidSigTerm → OpJoinSemilattice_RingoidSigTerm))  
      open OpJoinSemilattice_RingoidSigTerm 
  
  inductive OpJoinSemilattice_RingoidSigTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpJoinSemilattice_RingoidSigTerm2) 
     | sing2 : (A → OpJoinSemilattice_RingoidSigTerm2) 
     | plusOL2 : (OpJoinSemilattice_RingoidSigTerm2 → (OpJoinSemilattice_RingoidSigTerm2 → OpJoinSemilattice_RingoidSigTerm2)) 
     | timesOL2 : (OpJoinSemilattice_RingoidSigTerm2 → (OpJoinSemilattice_RingoidSigTerm2 → OpJoinSemilattice_RingoidSigTerm2))  
      open OpJoinSemilattice_RingoidSigTerm2 
  
  def simplifyCl   {A : Type}  : ((ClJoinSemilattice_RingoidSigTerm A) → (ClJoinSemilattice_RingoidSigTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpJoinSemilattice_RingoidSigTerm n) → (OpJoinSemilattice_RingoidSigTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpJoinSemilattice_RingoidSigTerm2 n A) → (OpJoinSemilattice_RingoidSigTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((JoinSemilattice_RingoidSig A) → (JoinSemilattice_RingoidSigTerm → A)) 
  | Jo (plusL x1 x2) := ((plus Jo) (evalB Jo x1) (evalB Jo x2))  
  | Jo (timesL x1 x2) := ((times Jo) (evalB Jo x1) (evalB Jo x2))  
  def evalCl   {A : Type}  : ((JoinSemilattice_RingoidSig A) → ((ClJoinSemilattice_RingoidSigTerm A) → A)) 
  | Jo (sing x1) := x1  
  | Jo (plusCl x1 x2) := ((plus Jo) (evalCl Jo x1) (evalCl Jo x2))  
  | Jo (timesCl x1 x2) := ((times Jo) (evalCl Jo x1) (evalCl Jo x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((JoinSemilattice_RingoidSig A) → ((vector A n) → ((OpJoinSemilattice_RingoidSigTerm n) → A))) 
  | Jo vars (v x1) := (nth vars x1)  
  | Jo vars (plusOL x1 x2) := ((plus Jo) (evalOpB Jo vars x1) (evalOpB Jo vars x2))  
  | Jo vars (timesOL x1 x2) := ((times Jo) (evalOpB Jo vars x1) (evalOpB Jo vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((JoinSemilattice_RingoidSig A) → ((vector A n) → ((OpJoinSemilattice_RingoidSigTerm2 n A) → A))) 
  | Jo vars (v2 x1) := (nth vars x1)  
  | Jo vars (sing2 x1) := x1  
  | Jo vars (plusOL2 x1 x2) := ((plus Jo) (evalOp Jo vars x1) (evalOp Jo vars x2))  
  | Jo vars (timesOL2 x1 x2) := ((times Jo) (evalOp Jo vars x1) (evalOp Jo vars x2))  
  def inductionB   {P : (JoinSemilattice_RingoidSigTerm → Type)}  : ((∀ (x1 x2 : JoinSemilattice_RingoidSigTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : JoinSemilattice_RingoidSigTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : JoinSemilattice_RingoidSigTerm) , (P x)))) 
  | pplusl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl ptimesl x1) (inductionB pplusl ptimesl x2))  
  | pplusl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl ptimesl x1) (inductionB pplusl ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClJoinSemilattice_RingoidSigTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClJoinSemilattice_RingoidSigTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClJoinSemilattice_RingoidSigTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClJoinSemilattice_RingoidSigTerm A)) , (P x))))) 
  | psing ppluscl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl ptimescl x1) (inductionCl psing ppluscl ptimescl x2))  
  | psing ppluscl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl ptimescl x1) (inductionCl psing ppluscl ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpJoinSemilattice_RingoidSigTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpJoinSemilattice_RingoidSigTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpJoinSemilattice_RingoidSigTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpJoinSemilattice_RingoidSigTerm n)) , (P x))))) 
  | pv pplusol ptimesol (v x1) := (pv x1)  
  | pv pplusol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol ptimesol x1) (inductionOpB pv pplusol ptimesol x2))  
  | pv pplusol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol ptimesol x1) (inductionOpB pv pplusol ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpJoinSemilattice_RingoidSigTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpJoinSemilattice_RingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpJoinSemilattice_RingoidSigTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpJoinSemilattice_RingoidSigTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 x2))  
  def stageB  : (JoinSemilattice_RingoidSigTerm → (Staged JoinSemilattice_RingoidSigTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClJoinSemilattice_RingoidSigTerm A) → (Staged (ClJoinSemilattice_RingoidSigTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpJoinSemilattice_RingoidSigTerm n) → (Staged (OpJoinSemilattice_RingoidSigTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpJoinSemilattice_RingoidSigTerm2 n A) → (Staged (OpJoinSemilattice_RingoidSigTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end JoinSemilattice_RingoidSig