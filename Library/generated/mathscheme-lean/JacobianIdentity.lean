import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section JacobianIdentity   
  structure JacobianIdentity  (A : Type) : Type := 
       (zero : A)
       (plus : (A → (A → A)))
       (times : (A → (A → A)))
       (jacobian_times_plus : (∀ {x y z : A} , (plus (plus (times x (times y z)) (times y (times z x))) (times z (times x y))) = zero)) 
  
  open JacobianIdentity
  structure Sig  (AS : Type) : Type := 
       (zeroS : AS)
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (zeroP : (Prod A A))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (jacobian_times_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP (timesP xP (timesP yP zP)) (timesP yP (timesP zP xP))) (timesP zP (timesP xP yP))) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ja1 : (JacobianIdentity A1)) (Ja2 : (JacobianIdentity A2)) : Type := 
       (hom : (A1 → A2))
       (pres_zero : (hom (zero Ja1)) = (zero Ja2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ja1) x1 x2)) = ((plus Ja2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times Ja1) x1 x2)) = ((times Ja2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ja1 : (JacobianIdentity A1)) (Ja2 : (JacobianIdentity A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_zero : (interp (zero Ja1) (zero Ja2)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ja1) x1 x2) ((plus Ja2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times Ja1) x1 x2) ((times Ja2) y1 y2)))))) 
  
  inductive JacobianIdentityTerm   : Type  
     | zeroL : JacobianIdentityTerm 
     | plusL : (JacobianIdentityTerm → (JacobianIdentityTerm → JacobianIdentityTerm)) 
     | timesL : (JacobianIdentityTerm → (JacobianIdentityTerm → JacobianIdentityTerm))  
      open JacobianIdentityTerm 
  
  inductive ClJacobianIdentityTerm  (A : Type) : Type  
     | sing : (A → ClJacobianIdentityTerm) 
     | zeroCl : ClJacobianIdentityTerm 
     | plusCl : (ClJacobianIdentityTerm → (ClJacobianIdentityTerm → ClJacobianIdentityTerm)) 
     | timesCl : (ClJacobianIdentityTerm → (ClJacobianIdentityTerm → ClJacobianIdentityTerm))  
      open ClJacobianIdentityTerm 
  
  inductive OpJacobianIdentityTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpJacobianIdentityTerm) 
     | zeroOL : OpJacobianIdentityTerm 
     | plusOL : (OpJacobianIdentityTerm → (OpJacobianIdentityTerm → OpJacobianIdentityTerm)) 
     | timesOL : (OpJacobianIdentityTerm → (OpJacobianIdentityTerm → OpJacobianIdentityTerm))  
      open OpJacobianIdentityTerm 
  
  inductive OpJacobianIdentityTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpJacobianIdentityTerm2) 
     | sing2 : (A → OpJacobianIdentityTerm2) 
     | zeroOL2 : OpJacobianIdentityTerm2 
     | plusOL2 : (OpJacobianIdentityTerm2 → (OpJacobianIdentityTerm2 → OpJacobianIdentityTerm2)) 
     | timesOL2 : (OpJacobianIdentityTerm2 → (OpJacobianIdentityTerm2 → OpJacobianIdentityTerm2))  
      open OpJacobianIdentityTerm2 
  
  def simplifyCl   (A : Type)  : ((ClJacobianIdentityTerm A) → (ClJacobianIdentityTerm A)) 
  | zeroCl := zeroCl  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpJacobianIdentityTerm n) → (OpJacobianIdentityTerm n)) 
  | zeroOL := zeroOL  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpJacobianIdentityTerm2 n A) → (OpJacobianIdentityTerm2 n A)) 
  | zeroOL2 := zeroOL2  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((JacobianIdentity A) → (JacobianIdentityTerm → A)) 
  | Ja zeroL := (zero Ja)  
  | Ja (plusL x1 x2) := ((plus Ja) (evalB Ja x1) (evalB Ja x2))  
  | Ja (timesL x1 x2) := ((times Ja) (evalB Ja x1) (evalB Ja x2))  
  def evalCl   {A : Type}  : ((JacobianIdentity A) → ((ClJacobianIdentityTerm A) → A)) 
  | Ja (sing x1) := x1  
  | Ja zeroCl := (zero Ja)  
  | Ja (plusCl x1 x2) := ((plus Ja) (evalCl Ja x1) (evalCl Ja x2))  
  | Ja (timesCl x1 x2) := ((times Ja) (evalCl Ja x1) (evalCl Ja x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((JacobianIdentity A) → ((vector A n) → ((OpJacobianIdentityTerm n) → A))) 
  | Ja vars (v x1) := (nth vars x1)  
  | Ja vars zeroOL := (zero Ja)  
  | Ja vars (plusOL x1 x2) := ((plus Ja) (evalOpB Ja vars x1) (evalOpB Ja vars x2))  
  | Ja vars (timesOL x1 x2) := ((times Ja) (evalOpB Ja vars x1) (evalOpB Ja vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((JacobianIdentity A) → ((vector A n) → ((OpJacobianIdentityTerm2 n A) → A))) 
  | Ja vars (v2 x1) := (nth vars x1)  
  | Ja vars (sing2 x1) := x1  
  | Ja vars zeroOL2 := (zero Ja)  
  | Ja vars (plusOL2 x1 x2) := ((plus Ja) (evalOp Ja vars x1) (evalOp Ja vars x2))  
  | Ja vars (timesOL2 x1 x2) := ((times Ja) (evalOp Ja vars x1) (evalOp Ja vars x2))  
  def inductionB   (P : (JacobianIdentityTerm → Type))  : ((P zeroL) → ((∀ (x1 x2 : JacobianIdentityTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : JacobianIdentityTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : JacobianIdentityTerm) , (P x))))) 
  | p0l pplusl ptimesl zeroL := p0l  
  | p0l pplusl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB p0l pplusl ptimesl x1) (inductionB p0l pplusl ptimesl x2))  
  | p0l pplusl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB p0l pplusl ptimesl x1) (inductionB p0l pplusl ptimesl x2))  
  def inductionCl   (A : Type) (P : ((ClJacobianIdentityTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P zeroCl) → ((∀ (x1 x2 : (ClJacobianIdentityTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClJacobianIdentityTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClJacobianIdentityTerm A)) , (P x)))))) 
  | psing p0cl ppluscl ptimescl (sing x1) := (psing x1)  
  | psing p0cl ppluscl ptimescl zeroCl := p0cl  
  | psing p0cl ppluscl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing p0cl ppluscl ptimescl x1) (inductionCl psing p0cl ppluscl ptimescl x2))  
  | psing p0cl ppluscl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing p0cl ppluscl ptimescl x1) (inductionCl psing p0cl ppluscl ptimescl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpJacobianIdentityTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P zeroOL) → ((∀ (x1 x2 : (OpJacobianIdentityTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpJacobianIdentityTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpJacobianIdentityTerm n)) , (P x)))))) 
  | pv p0ol pplusol ptimesol (v x1) := (pv x1)  
  | pv p0ol pplusol ptimesol zeroOL := p0ol  
  | pv p0ol pplusol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv p0ol pplusol ptimesol x1) (inductionOpB pv p0ol pplusol ptimesol x2))  
  | pv p0ol pplusol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv p0ol pplusol ptimesol x1) (inductionOpB pv p0ol pplusol ptimesol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpJacobianIdentityTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P zeroOL2) → ((∀ (x1 x2 : (OpJacobianIdentityTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpJacobianIdentityTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpJacobianIdentityTerm2 n A)) , (P x))))))) 
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 zeroOL2 := p0ol2  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x2))  
  | pv2 psing2 p0ol2 pplusol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 p0ol2 pplusol2 ptimesol2 x2))  
  def stageB  : (JacobianIdentityTerm → (Staged JacobianIdentityTerm))
  | zeroL := (Now zeroL)  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClJacobianIdentityTerm A) → (Staged (ClJacobianIdentityTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | zeroCl := (Now zeroCl)  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpJacobianIdentityTerm n) → (Staged (OpJacobianIdentityTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | zeroOL := (Now zeroOL)  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpJacobianIdentityTerm2 n A) → (Staged (OpJacobianIdentityTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | zeroOL2 := (Now zeroOL2)  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (zeroT : (Repr A))
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end JacobianIdentity