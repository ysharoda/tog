import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AdditiveGroup   
  structure AdditiveGroup  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero)) 
  
  open AdditiveGroup
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveGroup A1)) (Ad2 : (AdditiveGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ad1) x1 x2)) = ((plus Ad2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ad1)) = (zero Ad2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Ad1) x1)) = ((neg Ad2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ad1 : (AdditiveGroup A1)) (Ad2 : (AdditiveGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ad1) x1 x2) ((plus Ad2) y1 y2))))))
       (interp_zero : (interp (zero Ad1) (zero Ad2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Ad1) x1) ((neg Ad2) y1))))) 
  
  inductive AdditiveGroupTerm   : Type  
     | plusL : (AdditiveGroupTerm → (AdditiveGroupTerm → AdditiveGroupTerm)) 
     | zeroL : AdditiveGroupTerm 
     | negL : (AdditiveGroupTerm → AdditiveGroupTerm)  
      open AdditiveGroupTerm 
  
  inductive ClAdditiveGroupTerm  (A : Type) : Type  
     | sing : (A → ClAdditiveGroupTerm) 
     | plusCl : (ClAdditiveGroupTerm → (ClAdditiveGroupTerm → ClAdditiveGroupTerm)) 
     | zeroCl : ClAdditiveGroupTerm 
     | negCl : (ClAdditiveGroupTerm → ClAdditiveGroupTerm)  
      open ClAdditiveGroupTerm 
  
  inductive OpAdditiveGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAdditiveGroupTerm) 
     | plusOL : (OpAdditiveGroupTerm → (OpAdditiveGroupTerm → OpAdditiveGroupTerm)) 
     | zeroOL : OpAdditiveGroupTerm 
     | negOL : (OpAdditiveGroupTerm → OpAdditiveGroupTerm)  
      open OpAdditiveGroupTerm 
  
  inductive OpAdditiveGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAdditiveGroupTerm2) 
     | sing2 : (A → OpAdditiveGroupTerm2) 
     | plusOL2 : (OpAdditiveGroupTerm2 → (OpAdditiveGroupTerm2 → OpAdditiveGroupTerm2)) 
     | zeroOL2 : OpAdditiveGroupTerm2 
     | negOL2 : (OpAdditiveGroupTerm2 → OpAdditiveGroupTerm2)  
      open OpAdditiveGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAdditiveGroupTerm A) → (ClAdditiveGroupTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAdditiveGroupTerm n) → (OpAdditiveGroupTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAdditiveGroupTerm2 n A) → (OpAdditiveGroupTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AdditiveGroup A) → (AdditiveGroupTerm → A)) 
  | Ad (plusL x1 x2) := ((plus Ad) (evalB Ad x1) (evalB Ad x2))  
  | Ad zeroL := (zero Ad)  
  | Ad (negL x1) := ((neg Ad) (evalB Ad x1))  
  def evalCl   {A : Type}  : ((AdditiveGroup A) → ((ClAdditiveGroupTerm A) → A)) 
  | Ad (sing x1) := x1  
  | Ad (plusCl x1 x2) := ((plus Ad) (evalCl Ad x1) (evalCl Ad x2))  
  | Ad zeroCl := (zero Ad)  
  | Ad (negCl x1) := ((neg Ad) (evalCl Ad x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AdditiveGroup A) → ((vector A n) → ((OpAdditiveGroupTerm n) → A))) 
  | Ad vars (v x1) := (nth vars x1)  
  | Ad vars (plusOL x1 x2) := ((plus Ad) (evalOpB Ad vars x1) (evalOpB Ad vars x2))  
  | Ad vars zeroOL := (zero Ad)  
  | Ad vars (negOL x1) := ((neg Ad) (evalOpB Ad vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((AdditiveGroup A) → ((vector A n) → ((OpAdditiveGroupTerm2 n A) → A))) 
  | Ad vars (v2 x1) := (nth vars x1)  
  | Ad vars (sing2 x1) := x1  
  | Ad vars (plusOL2 x1 x2) := ((plus Ad) (evalOp Ad vars x1) (evalOp Ad vars x2))  
  | Ad vars zeroOL2 := (zero Ad)  
  | Ad vars (negOL2 x1) := ((neg Ad) (evalOp Ad vars x1))  
  def inductionB   (P : (AdditiveGroupTerm → Type))  : ((∀ (x1 x2 : AdditiveGroupTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : AdditiveGroupTerm) , ((P x1) → (P (negL x1)))) → (∀ (x : AdditiveGroupTerm) , (P x))))) 
  | pplusl p0l pnegl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l pnegl x1) (inductionB pplusl p0l pnegl x2))  
  | pplusl p0l pnegl zeroL := p0l  
  | pplusl p0l pnegl (negL x1) := (pnegl _ (inductionB pplusl p0l pnegl x1))  
  def inductionCl   (A : Type) (P : ((ClAdditiveGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAdditiveGroupTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClAdditiveGroupTerm A)) , ((P x1) → (P (negCl x1)))) → (∀ (x : (ClAdditiveGroupTerm A)) , (P x)))))) 
  | psing ppluscl p0cl pnegcl (sing x1) := (psing x1)  
  | psing ppluscl p0cl pnegcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl pnegcl x1) (inductionCl psing ppluscl p0cl pnegcl x2))  
  | psing ppluscl p0cl pnegcl zeroCl := p0cl  
  | psing ppluscl p0cl pnegcl (negCl x1) := (pnegcl _ (inductionCl psing ppluscl p0cl pnegcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpAdditiveGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAdditiveGroupTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpAdditiveGroupTerm n)) , ((P x1) → (P (negOL x1)))) → (∀ (x : (OpAdditiveGroupTerm n)) , (P x)))))) 
  | pv pplusol p0ol pnegol (v x1) := (pv x1)  
  | pv pplusol p0ol pnegol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol pnegol x1) (inductionOpB pv pplusol p0ol pnegol x2))  
  | pv pplusol p0ol pnegol zeroOL := p0ol  
  | pv pplusol p0ol pnegol (negOL x1) := (pnegol _ (inductionOpB pv pplusol p0ol pnegol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAdditiveGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAdditiveGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpAdditiveGroupTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → (∀ (x : (OpAdditiveGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 zeroOL2 := p0ol2  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 x1))  
  def stageB  : (AdditiveGroupTerm → (Staged AdditiveGroupTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClAdditiveGroupTerm A) → (Staged (ClAdditiveGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpAdditiveGroupTerm n) → (Staged (OpAdditiveGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAdditiveGroupTerm2 n A) → (Staged (OpAdditiveGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A))) 
  
end AdditiveGroup