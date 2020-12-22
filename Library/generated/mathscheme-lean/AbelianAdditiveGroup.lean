import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section AbelianAdditiveGroup   
  structure AbelianAdditiveGroup  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (associative_plus : (∀ {x y z : A} , (plus (plus x y) z) = (plus x (plus y z))))
       (zero : A)
       (lunit_zero : (∀ {x : A} , (plus zero x) = x))
       (runit_zero : (∀ {x : A} , (plus x zero) = x))
       (commutative_plus : (∀ {x y : A} , (plus x y) = (plus y x)))
       (neg : (A → A))
       (leftInverse_inv_op_zero : (∀ {x : A} , (plus x (neg x)) = zero))
       (rightInverse_inv_op_zero : (∀ {x : A} , (plus (neg x) x) = zero)) 
  
  open AbelianAdditiveGroup
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (zeroS : AS)
       (negS : (AS → AS)) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (zeroP : (Prod A A))
       (negP : ((Prod A A) → (Prod A A)))
       (associative_plusP : (∀ {xP yP zP : (Prod A A)} , (plusP (plusP xP yP) zP) = (plusP xP (plusP yP zP))))
       (lunit_0P : (∀ {xP : (Prod A A)} , (plusP zeroP xP) = xP))
       (runit_0P : (∀ {xP : (Prod A A)} , (plusP xP zeroP) = xP))
       (commutative_plusP : (∀ {xP yP : (Prod A A)} , (plusP xP yP) = (plusP yP xP)))
       (leftInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP xP (negP xP)) = zeroP))
       (rightInverse_inv_op_0P : (∀ {xP : (Prod A A)} , (plusP (negP xP) xP) = zeroP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Ab1 : (AbelianAdditiveGroup A1)) (Ab2 : (AbelianAdditiveGroup A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Ab1) x1 x2)) = ((plus Ab2) (hom x1) (hom x2))))
       (pres_zero : (hom (zero Ab1)) = (zero Ab2))
       (pres_neg : (∀ {x1 : A1} , (hom ((neg Ab1) x1)) = ((neg Ab2) (hom x1)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ab1 : (AbelianAdditiveGroup A1)) (Ab2 : (AbelianAdditiveGroup A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Ab1) x1 x2) ((plus Ab2) y1 y2))))))
       (interp_zero : (interp (zero Ab1) (zero Ab2)))
       (interp_neg : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((neg Ab1) x1) ((neg Ab2) y1))))) 
  
  inductive AbelianAdditiveGroupTerm   : Type  
     | plusL : (AbelianAdditiveGroupTerm → (AbelianAdditiveGroupTerm → AbelianAdditiveGroupTerm)) 
     | zeroL : AbelianAdditiveGroupTerm 
     | negL : (AbelianAdditiveGroupTerm → AbelianAdditiveGroupTerm)  
      open AbelianAdditiveGroupTerm 
  
  inductive ClAbelianAdditiveGroupTerm  (A : Type) : Type  
     | sing : (A → ClAbelianAdditiveGroupTerm) 
     | plusCl : (ClAbelianAdditiveGroupTerm → (ClAbelianAdditiveGroupTerm → ClAbelianAdditiveGroupTerm)) 
     | zeroCl : ClAbelianAdditiveGroupTerm 
     | negCl : (ClAbelianAdditiveGroupTerm → ClAbelianAdditiveGroupTerm)  
      open ClAbelianAdditiveGroupTerm 
  
  inductive OpAbelianAdditiveGroupTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpAbelianAdditiveGroupTerm) 
     | plusOL : (OpAbelianAdditiveGroupTerm → (OpAbelianAdditiveGroupTerm → OpAbelianAdditiveGroupTerm)) 
     | zeroOL : OpAbelianAdditiveGroupTerm 
     | negOL : (OpAbelianAdditiveGroupTerm → OpAbelianAdditiveGroupTerm)  
      open OpAbelianAdditiveGroupTerm 
  
  inductive OpAbelianAdditiveGroupTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpAbelianAdditiveGroupTerm2) 
     | sing2 : (A → OpAbelianAdditiveGroupTerm2) 
     | plusOL2 : (OpAbelianAdditiveGroupTerm2 → (OpAbelianAdditiveGroupTerm2 → OpAbelianAdditiveGroupTerm2)) 
     | zeroOL2 : OpAbelianAdditiveGroupTerm2 
     | negOL2 : (OpAbelianAdditiveGroupTerm2 → OpAbelianAdditiveGroupTerm2)  
      open OpAbelianAdditiveGroupTerm2 
  
  def simplifyCl   (A : Type)  : ((ClAbelianAdditiveGroupTerm A) → (ClAbelianAdditiveGroupTerm A)) 
  | (plusCl zeroCl x) := x  
  | (plusCl x zeroCl) := x  
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | zeroCl := zeroCl  
  | (negCl x1) := (negCl (simplifyCl x1))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpAbelianAdditiveGroupTerm n) → (OpAbelianAdditiveGroupTerm n)) 
  | (plusOL zeroOL x) := x  
  | (plusOL x zeroOL) := x  
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | zeroOL := zeroOL  
  | (negOL x1) := (negOL (simplifyOpB x1))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpAbelianAdditiveGroupTerm2 n A) → (OpAbelianAdditiveGroupTerm2 n A)) 
  | (plusOL2 zeroOL2 x) := x  
  | (plusOL2 x zeroOL2) := x  
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | zeroOL2 := zeroOL2  
  | (negOL2 x1) := (negOL2 (simplifyOp x1))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((AbelianAdditiveGroup A) → (AbelianAdditiveGroupTerm → A)) 
  | Ab (plusL x1 x2) := ((plus Ab) (evalB Ab x1) (evalB Ab x2))  
  | Ab zeroL := (zero Ab)  
  | Ab (negL x1) := ((neg Ab) (evalB Ab x1))  
  def evalCl   {A : Type}  : ((AbelianAdditiveGroup A) → ((ClAbelianAdditiveGroupTerm A) → A)) 
  | Ab (sing x1) := x1  
  | Ab (plusCl x1 x2) := ((plus Ab) (evalCl Ab x1) (evalCl Ab x2))  
  | Ab zeroCl := (zero Ab)  
  | Ab (negCl x1) := ((neg Ab) (evalCl Ab x1))  
  def evalOpB   {A : Type} (n : ℕ)  : ((AbelianAdditiveGroup A) → ((vector A n) → ((OpAbelianAdditiveGroupTerm n) → A))) 
  | Ab vars (v x1) := (nth vars x1)  
  | Ab vars (plusOL x1 x2) := ((plus Ab) (evalOpB Ab vars x1) (evalOpB Ab vars x2))  
  | Ab vars zeroOL := (zero Ab)  
  | Ab vars (negOL x1) := ((neg Ab) (evalOpB Ab vars x1))  
  def evalOp   {A : Type} (n : ℕ)  : ((AbelianAdditiveGroup A) → ((vector A n) → ((OpAbelianAdditiveGroupTerm2 n A) → A))) 
  | Ab vars (v2 x1) := (nth vars x1)  
  | Ab vars (sing2 x1) := x1  
  | Ab vars (plusOL2 x1 x2) := ((plus Ab) (evalOp Ab vars x1) (evalOp Ab vars x2))  
  | Ab vars zeroOL2 := (zero Ab)  
  | Ab vars (negOL2 x1) := ((neg Ab) (evalOp Ab vars x1))  
  def inductionB   (P : (AbelianAdditiveGroupTerm → Type))  : ((∀ (x1 x2 : AbelianAdditiveGroupTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P zeroL) → ((∀ (x1 : AbelianAdditiveGroupTerm) , ((P x1) → (P (negL x1)))) → (∀ (x : AbelianAdditiveGroupTerm) , (P x))))) 
  | pplusl p0l pnegl (plusL x1 x2) := (pplusl _ _ (inductionB pplusl p0l pnegl x1) (inductionB pplusl p0l pnegl x2))  
  | pplusl p0l pnegl zeroL := p0l  
  | pplusl p0l pnegl (negL x1) := (pnegl _ (inductionB pplusl p0l pnegl x1))  
  def inductionCl   (A : Type) (P : ((ClAbelianAdditiveGroupTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClAbelianAdditiveGroupTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P zeroCl) → ((∀ (x1 : (ClAbelianAdditiveGroupTerm A)) , ((P x1) → (P (negCl x1)))) → (∀ (x : (ClAbelianAdditiveGroupTerm A)) , (P x)))))) 
  | psing ppluscl p0cl pnegcl (sing x1) := (psing x1)  
  | psing ppluscl p0cl pnegcl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl p0cl pnegcl x1) (inductionCl psing ppluscl p0cl pnegcl x2))  
  | psing ppluscl p0cl pnegcl zeroCl := p0cl  
  | psing ppluscl p0cl pnegcl (negCl x1) := (pnegcl _ (inductionCl psing ppluscl p0cl pnegcl x1))  
  def inductionOpB   (n : ℕ) (P : ((OpAbelianAdditiveGroupTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpAbelianAdditiveGroupTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P zeroOL) → ((∀ (x1 : (OpAbelianAdditiveGroupTerm n)) , ((P x1) → (P (negOL x1)))) → (∀ (x : (OpAbelianAdditiveGroupTerm n)) , (P x)))))) 
  | pv pplusol p0ol pnegol (v x1) := (pv x1)  
  | pv pplusol p0ol pnegol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol p0ol pnegol x1) (inductionOpB pv pplusol p0ol pnegol x2))  
  | pv pplusol p0ol pnegol zeroOL := p0ol  
  | pv pplusol p0ol pnegol (negOL x1) := (pnegol _ (inductionOpB pv pplusol p0ol pnegol x1))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpAbelianAdditiveGroupTerm2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpAbelianAdditiveGroupTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P zeroOL2) → ((∀ (x1 : (OpAbelianAdditiveGroupTerm2 n A)) , ((P x1) → (P (negOL2 x1)))) → (∀ (x : (OpAbelianAdditiveGroupTerm2 n A)) , (P x))))))) 
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 x2))  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 zeroOL2 := p0ol2  
  | pv2 psing2 pplusol2 p0ol2 pnegol2 (negOL2 x1) := (pnegol2 _ (inductionOp pv2 psing2 pplusol2 p0ol2 pnegol2 x1))  
  def stageB  : (AbelianAdditiveGroupTerm → (Staged AbelianAdditiveGroupTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | zeroL := (Now zeroL)  
  | (negL x1) := (stage1 negL (codeLift1 negL) (stageB x1))  
  def stageCl   (A : Type)  : ((ClAbelianAdditiveGroupTerm A) → (Staged (ClAbelianAdditiveGroupTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | zeroCl := (Now zeroCl)  
  | (negCl x1) := (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  def stageOpB   (n : ℕ)  : ((OpAbelianAdditiveGroupTerm n) → (Staged (OpAbelianAdditiveGroupTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | zeroOL := (Now zeroOL)  
  | (negOL x1) := (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpAbelianAdditiveGroupTerm2 n A) → (Staged (OpAbelianAdditiveGroupTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | zeroOL2 := (Now zeroOL2)  
  | (negOL2 x1) := (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (zeroT : (Repr A))
       (negT : ((Repr A) → (Repr A))) 
  
end AbelianAdditiveGroup