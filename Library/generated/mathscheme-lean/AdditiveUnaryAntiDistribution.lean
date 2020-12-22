import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AdditiveUnaryAntiDistribution   
  structure AdditiveUnaryAntiDistribution  (A : Type) : Type := 
       (prim : (A → A))
       (plus : (A → (A → A)))
       (antidis_prim_plus : (∀ {x y : A} , (prim (plus x y)) = (plus (prim y) (prim x)))) 
  
  open AdditiveUnaryAntiDistribution
  structure Sig  (AS : Type) : Type := 
       (primS : (AS → AS))
       (plusS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (primP : ((Prod A A) → (Prod A A)))
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (antidis_prim_plusP : (∀ {xP yP : (Prod A A)} , (primP (plusP xP yP)) = (plusP (primP yP) (primP xP)))) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveUnaryAntiDistribution A1)) (Ad2 : (AdditiveUnaryAntiDistribution A2)) : Type := 
       (hom : (A1 → A2))
       (pres_prim : (∀ {x1 : A1} , (hom ((prim Ad1) x1)) = ((prim Ad2) (hom x1))))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveUnaryAntiDistribution A1)) (Ad2 : (AdditiveUnaryAntiDistribution A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_prim : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((prim Ad1) x1) ((prim Ad2) y1)))))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2)))))) 
  
  inductive AdditiveUnaryAntiDistributionTerm   : Type  
     | primL : (AdditiveUnaryAntiDistributionTerm → AdditiveUnaryAntiDistributionTerm) 
     | plusL : (AdditiveUnaryAntiDistributionTerm → (AdditiveUnaryAntiDistributionTerm → AdditiveUnaryAntiDistributionTerm))  
      open AdditiveUnaryAntiDistributionTerm 
  
  inductive ClAdditiveUnaryAntiDistributionTerm  (A : Type) : Type  
     | sing : (A → ClAdditiveUnaryAntiDistributionTerm) 
     | primCl : (ClAdditiveUnaryAntiDistributionTerm → ClAdditiveUnaryAntiDistributionTerm) 
     | plusCl : (ClAdditiveUnaryAntiDistributionTerm → (ClAdditiveUnaryAntiDistributionTerm → ClAdditiveUnaryAntiDistributionTerm))  
      open ClAdditiveUnaryAntiDistributionTerm 
  
  inductive OpAdditiveUnaryAntiDistributionTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAdditiveUnaryAntiDistributionTerm) 
     | primOL : (OpAdditiveUnaryAntiDistributionTerm → OpAdditiveUnaryAntiDistributionTerm) 
     | plusOL : (OpAdditiveUnaryAntiDistributionTerm → (OpAdditiveUnaryAntiDistributionTerm → OpAdditiveUnaryAntiDistributionTerm))  
      open OpAdditiveUnaryAntiDistributionTerm 
  
  inductive OpAdditiveUnaryAntiDistributionTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAdditiveUnaryAntiDistributionTerm2) 
     | sing2 : (A → OpAdditiveUnaryAntiDistributionTerm2) 
     | primOL2 : (OpAdditiveUnaryAntiDistributionTerm2 → OpAdditiveUnaryAntiDistributionTerm2) 
     | plusOL2 : (OpAdditiveUnaryAntiDistributionTerm2 → (OpAdditiveUnaryAntiDistributionTerm2 → OpAdditiveUnaryAntiDistributionTerm2))  
      open OpAdditiveUnaryAntiDistributionTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAdditiveUnaryAntiDistributionTerm A) → (ClAdditiveUnaryAntiDistributionTerm A)) 
  | (plusCl (primCl y) (primCl x)) := (primCl (plusCl x y))  
  | (primCl x1) := (primCl (simplifyCl x1))  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAdditiveUnaryAntiDistributionTerm n) → (OpAdditiveUnaryAntiDistributionTerm n)) 
  | (plusOL (primOL y) (primOL x)) := (primOL (plusOL x y))  
  | (primOL x1) := (primOL (simplifyOpB x1))  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAdditiveUnaryAntiDistributionTerm2 n A) → (OpAdditiveUnaryAntiDistributionTerm2 n A)) 
  | (plusOL2 (primOL2 y) (primOL2 x)) := (primOL2 (plusOL2 x y))  
  | (primOL2 x1) := (primOL2 (simplifyOp x1))  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AdditiveUnaryAntiDistribution A) → (AdditiveUnaryAntiDistributionTerm → A)) 
  | Ad (primL x1) := ((prim Ad) (evalB Ad x1))  
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  def evalCl   {A : Type}  : ((AdditiveUnaryAntiDistribution A) → ((ClAdditiveUnaryAntiDistributionTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad (primCl x1) := ((prim Ad) (evalCl Ad x1))  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AdditiveUnaryAntiDistribution A) → ((vector A n) → ((OpAdditiveUnaryAntiDistributionTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars (primOL x1) := ((prim Ad) (evalOpB Ad vars x1))  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((AdditiveUnaryAntiDistribution A) → ((vector A n) → ((OpAdditiveUnaryAntiDistributionTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars (primOL2 x1) := ((prim Ad) (evalOp Ad vars x1))  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  def inductionB   (P : (AdditiveUnaryAntiDistributionTerm → Type))  : ((∀ (x1 : AdditiveUnaryAntiDistributionTerm) , ((P x1) → (P (primL x1)))) → ((∀ (x1 x2 : AdditiveUnaryAntiDistributionTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → (∀ (x : AdditiveUnaryAntiDistributionTerm) , (P x)))) 
  | ppriml pplusl (primL x1) := (ppriml _ (inductionB ppriml pplusl x1))  
  | ppriml pplusl (plusL x1 x2) := (pplusl _ _ (inductionB ppriml pplusl x1) (inductionB ppriml pplusl x2))  
  def inductionCl   (A : Type) (P : ((ClAdditiveUnaryAntiDistributionTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClAdditiveUnaryAntiDistributionTerm A)) , ((P x1) → (P (primCl x1)))) → ((∀ (x1 x2 : (ClAdditiveUnaryAntiDistributionTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → (∀ (x : (ClAdditiveUnaryAntiDistributionTerm A)) , (P x))))) 
  | psing pprimcl ppluscl (sing x1) := (psing x1)  
  | psing pprimcl ppluscl (primCl x1) := (pprimcl _ (inductionCl psing pprimcl ppluscl x1))  
  | psing pprimcl ppluscl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing pprimcl ppluscl x1) (inductionCl psing pprimcl ppluscl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpAdditiveUnaryAntiDistributionTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpAdditiveUnaryAntiDistributionTerm n)) , ((P x1) → (P (primOL x1)))) → ((∀ (x1 x2 : (OpAdditiveUnaryAntiDistributionTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → (∀ (x : (OpAdditiveUnaryAntiDistributionTerm n)) , (P x))))) 
  | pv pprimol pplusol (v x1) := (pv x1)  
  | pv pprimol pplusol (primOL x1) := (pprimol _ (inductionOpB pv pprimol pplusol x1))  
  | pv pprimol pplusol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pprimol pplusol x1) (inductionOpB pv pprimol pplusol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAdditiveUnaryAntiDistributionTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpAdditiveUnaryAntiDistributionTerm2 n A)) , ((P x1) → (P (primOL2 x1)))) → ((∀ (x1 x2 : (OpAdditiveUnaryAntiDistributionTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → (∀ (x : (OpAdditiveUnaryAntiDistributionTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pprimol2 pplusol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pprimol2 pplusol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pprimol2 pplusol2 (primOL2 x1) := (pprimol2 _ (inductionOp pv2 psing2 pprimol2 pplusol2 x1))  
  | pv2 psing2 pprimol2 pplusol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pprimol2 pplusol2 x1) (inductionOp pv2 psing2 pprimol2 pplusol2 x2))  
  def stageB  : (AdditiveUnaryAntiDistributionTerm → (Staged AdditiveUnaryAntiDistributionTerm))
  | (primL x1) := (stage1 primL (codeLift1 primL) (stageB x1))  
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClAdditiveUnaryAntiDistributionTerm A) → (Staged (ClAdditiveUnaryAntiDistributionTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (primCl x1) := (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpAdditiveUnaryAntiDistributionTerm n) → (Staged (OpAdditiveUnaryAntiDistributionTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (primOL x1) := (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAdditiveUnaryAntiDistributionTerm2 n A) → (Staged (OpAdditiveUnaryAntiDistributionTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (primOL2 x1) := (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (primT : ((Repr A) → (Repr A)))
       (plusT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end AdditiveUnaryAntiDistribution