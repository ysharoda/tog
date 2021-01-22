import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AssocPlusRingoid   
  structure AssocPlusRingoid  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (times : (A → (A → A)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z)))) 
  
  open AssocPlusRingoid
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (timesS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (timesP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (As1 : (AssocPlusRingoid A1)) (As2 : (AssocPlusRingoid A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus As1) x1 x2)) = ((plus As2) (hom x1) (hom x2))))
       (pres_times : (∀ {x1 x2 : A1} , (hom ((times As1) x1 x2)) = ((times As2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (As1 : (AssocPlusRingoid A1)) (As2 : (AssocPlusRingoid A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus As1) x1 x2) ((plus As2) y1 y2))))))
       (interp_times : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((times As1) x1 x2) ((times As2) y1 y2)))))) 
  
  inductive AssocPlusRingoidTerm   : Type  
     | plusL : (AssocPlusRingoidTerm → (AssocPlusRingoidTerm → AssocPlusRingoidTerm)) 
     | timesL : (AssocPlusRingoidTerm → (AssocPlusRingoidTerm → AssocPlusRingoidTerm))  
      open AssocPlusRingoidTerm 
  
  inductive ClAssocPlusRingoidTerm  (A : Type) : Type  
     | sing : (A → ClAssocPlusRingoidTerm) 
     | plusCl : (ClAssocPlusRingoidTerm → (ClAssocPlusRingoidTerm → ClAssocPlusRingoidTerm)) 
     | timesCl : (ClAssocPlusRingoidTerm → (ClAssocPlusRingoidTerm → ClAssocPlusRingoidTerm))  
      open ClAssocPlusRingoidTerm 
  
  inductive OpAssocPlusRingoidTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAssocPlusRingoidTerm) 
     | plusOL : (OpAssocPlusRingoidTerm → (OpAssocPlusRingoidTerm → OpAssocPlusRingoidTerm)) 
     | timesOL : (OpAssocPlusRingoidTerm → (OpAssocPlusRingoidTerm → OpAssocPlusRingoidTerm))  
      open OpAssocPlusRingoidTerm 
  
  inductive OpAssocPlusRingoidTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAssocPlusRingoidTerm2) 
     | sing2 : (A → OpAssocPlusRingoidTerm2) 
     | plusOL2 : (OpAssocPlusRingoidTerm2 → (OpAssocPlusRingoidTerm2 → OpAssocPlusRingoidTerm2)) 
     | timesOL2 : (OpAssocPlusRingoidTerm2 → (OpAssocPlusRingoidTerm2 → OpAssocPlusRingoidTerm2))  
      open OpAssocPlusRingoidTerm2 
  
  def simplifyCl   {A : Type}  : ((ClAssocPlusRingoidTerm A) → (ClAssocPlusRingoidTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (timesCl x1 x2) := (timesCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpAssocPlusRingoidTerm n) → (OpAssocPlusRingoidTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (timesOL x1 x2) := (timesOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpAssocPlusRingoidTerm2 n A) → (OpAssocPlusRingoidTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (timesOL2 x1 x2) := (timesOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AssocPlusRingoid A) → (AssocPlusRingoidTerm → A)) 
  | As (plusL x1 x2) := ((plus As) (evalB As x1) (evalB As x2))  
  | As (timesL x1 x2) := ((times As) (evalB As x1) (evalB As x2))  
  def evalCl   {A : Type}  : ((AssocPlusRingoid A) → ((ClAssocPlusRingoidTerm A) → A)) 
  | As (sing x1) := x1  
  | As (plusCl x1 x2) := ((plus As) (evalCl As x1) (evalCl As x2))  
  | As (timesCl x1 x2) := ((times As) (evalCl As x1) (evalCl As x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((AssocPlusRingoid A) → ((vector A n) → ((OpAssocPlusRingoidTerm n) → A))) 
  | As vars (v x1) := (nth vars x1)  
  | As vars (plusOL x1 x2) := ((plus As) (evalOpB As vars x1) (evalOpB As vars x2))  
  | As vars (timesOL x1 x2) := ((times As) (evalOpB As vars x1) (evalOpB As vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((AssocPlusRingoid A) → ((vector A n) → ((OpAssocPlusRingoidTerm2 n A) → A))) 
  | As vars (v2 x1) := (nth vars x1)  
  | As vars (sing2 x1) := x1  
  | As vars (plusOL2 x1 x2) := ((plus As) (evalOp As vars x1) (evalOp As vars x2))  
  | As vars (timesOL2 x1 x2) := ((times As) (evalOp As vars x1) (evalOp As vars x2))  
  def inductionB   {P : (AssocPlusRingoidTerm → Type)}  : ((∀ (x1 x2 : AssocPlusRingoidTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((∀ (x1 x2 : AssocPlusRingoidTerm) , ((P x1) → ((P x2) → (P (timesL x1 x2))))) → (∀ (x : AssocPlusRingoidTerm) , (P x)))) 
  | pplusl ptimesl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl ptimesl x1) (inductionB pplusl ptimesl x2))  
  | pplusl ptimesl (timesL x1 x2) := (ptimesl _ _ (inductionB pplusl ptimesl x1) (inductionB pplusl ptimesl x2))  
  def inductionCl   {A : Type} {P : ((ClAssocPlusRingoidTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAssocPlusRingoidTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((∀ (x1 x2 : (ClAssocPlusRingoidTerm A)) , ((P x1) → ((P x2) → (P (timesCl x1 x2))))) → (∀ (x : (ClAssocPlusRingoidTerm A)) , (P x))))) 
  | psing ppluscl ptimescl (sing x1) := (psing x1)  
  | psing ppluscl ptimescl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl ptimescl x1) (inductionCl psing ppluscl ptimescl x2))  
  | psing ppluscl ptimescl (timesCl x1 x2) := (ptimescl _ _ (inductionCl psing ppluscl ptimescl x1) (inductionCl psing ppluscl ptimescl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpAssocPlusRingoidTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAssocPlusRingoidTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((∀ (x1 x2 : (OpAssocPlusRingoidTerm n)) , ((P x1) → ((P x2) → (P (timesOL x1 x2))))) → (∀ (x : (OpAssocPlusRingoidTerm n)) , (P x))))) 
  | pv pplusol ptimesol (v x1) := (pv x1)  
  | pv pplusol ptimesol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol ptimesol x1) (inductionOpB pv pplusol ptimesol x2))  
  | pv pplusol ptimesol (timesOL x1 x2) := (ptimesol _ _ (inductionOpB pv pplusol ptimesol x1) (inductionOpB pv pplusol ptimesol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpAssocPlusRingoidTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAssocPlusRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((∀ (x1 x2 : (OpAssocPlusRingoidTerm2 n A)) , ((P x1) → ((P x2) → (P (timesOL2 x1 x2))))) → (∀ (x : (OpAssocPlusRingoidTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 ptimesol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 ptimesol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 x2))  
  | pv2 psing2 pplusol2 ptimesol2 (timesOL2 x1 x2) := (ptimesol2 _ _ (inductionOp pv2 psing2 pplusol2 ptimesol2 x1) (inductionOp pv2 psing2 pplusol2 ptimesol2 x2))  
  def stageB  : (AssocPlusRingoidTerm → (Staged AssocPlusRingoidTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | (timesL x1 x2) := (stage2 timesL (codeLift2 timesL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClAssocPlusRingoidTerm A) → (Staged (ClAssocPlusRingoidTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | (timesCl x1 x2) := (stage2 timesCl (codeLift2 timesCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpAssocPlusRingoidTerm n) → (Staged (OpAssocPlusRingoidTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | (timesOL x1 x2) := (stage2 timesOL (codeLift2 timesOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpAssocPlusRingoidTerm2 n A) → (Staged (OpAssocPlusRingoidTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | (timesOL2 x1 x2) := (stage2 timesOL2 (codeLift2 timesOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (timesT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AssocPlusRingoid