import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section PointedPlusMagma   
  structure PointedPlusMagma  (A : Type) : Type := 
       (plus : (A → (A → A)))
       (e : A) 
  
  open PointedPlusMagma
  structure Sig  (AS : Type) : Type := 
       (plusS : (AS → (AS → AS)))
       (eS : AS) 
  
  structure Product  (A : Type) : Type := 
       (plusP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Po1 : (PointedPlusMagma A1)) (Po2 : (PointedPlusMagma A2)) : Type := 
       (hom : (A1 → A2))
       (pres_plus : (∀ {x1 x2 : A1} , (hom ((plus Po1) x1 x2)) = ((plus Po2) (hom x1) (hom x2))))
       (pres_e : (hom (e Po1)) = (e Po2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Po1 : (PointedPlusMagma A1)) (Po2 : (PointedPlusMagma A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_plus : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((plus Po1) x1 x2) ((plus Po2) y1 y2))))))
       (interp_e : (interp (e Po1) (e Po2))) 
  
  inductive PointedPlusMagmaTerm   : Type  
     | plusL : (PointedPlusMagmaTerm → (PointedPlusMagmaTerm → PointedPlusMagmaTerm)) 
     | eL : PointedPlusMagmaTerm  
      open PointedPlusMagmaTerm 
  
  inductive ClPointedPlusMagmaTerm  (A : Type) : Type  
     | sing : (A → ClPointedPlusMagmaTerm) 
     | plusCl : (ClPointedPlusMagmaTerm → (ClPointedPlusMagmaTerm → ClPointedPlusMagmaTerm)) 
     | eCl : ClPointedPlusMagmaTerm  
      open ClPointedPlusMagmaTerm 
  
  inductive OpPointedPlusMagmaTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpPointedPlusMagmaTerm) 
     | plusOL : (OpPointedPlusMagmaTerm → (OpPointedPlusMagmaTerm → OpPointedPlusMagmaTerm)) 
     | eOL : OpPointedPlusMagmaTerm  
      open OpPointedPlusMagmaTerm 
  
  inductive OpPointedPlusMagmaTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpPointedPlusMagmaTerm2) 
     | sing2 : (A → OpPointedPlusMagmaTerm2) 
     | plusOL2 : (OpPointedPlusMagmaTerm2 → (OpPointedPlusMagmaTerm2 → OpPointedPlusMagmaTerm2)) 
     | eOL2 : OpPointedPlusMagmaTerm2  
      open OpPointedPlusMagmaTerm2 
  
  def simplifyCl   {A : Type}  : ((ClPointedPlusMagmaTerm A) → (ClPointedPlusMagmaTerm A)) 
  | (plusCl x1 x2) := (plusCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpPointedPlusMagmaTerm n) → (OpPointedPlusMagmaTerm n)) 
  | (plusOL x1 x2) := (plusOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpPointedPlusMagmaTerm2 n A) → (OpPointedPlusMagmaTerm2 n A)) 
  | (plusOL2 x1 x2) := (plusOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((PointedPlusMagma A) → (PointedPlusMagmaTerm → A)) 
  | Po (plusL x1 x2) := ((plus Po) (evalB Po x1) (evalB Po x2))  
  | Po eL := (e Po)  
  def evalCl   {A : Type}  : ((PointedPlusMagma A) → ((ClPointedPlusMagmaTerm A) → A)) 
  | Po (sing x1) := x1  
  | Po (plusCl x1 x2) := ((plus Po) (evalCl Po x1) (evalCl Po x2))  
  | Po eCl := (e Po)  
  def evalOpB   {A : Type} {n : ℕ}  : ((PointedPlusMagma A) → ((vector A n) → ((OpPointedPlusMagmaTerm n) → A))) 
  | Po vars (v x1) := (nth vars x1)  
  | Po vars (plusOL x1 x2) := ((plus Po) (evalOpB Po vars x1) (evalOpB Po vars x2))  
  | Po vars eOL := (e Po)  
  def evalOp   {A : Type} {n : ℕ}  : ((PointedPlusMagma A) → ((vector A n) → ((OpPointedPlusMagmaTerm2 n A) → A))) 
  | Po vars (v2 x1) := (nth vars x1)  
  | Po vars (sing2 x1) := x1  
  | Po vars (plusOL2 x1 x2) := ((plus Po) (evalOp Po vars x1) (evalOp Po vars x2))  
  | Po vars eOL2 := (e Po)  
  def inductionB   {P : (PointedPlusMagmaTerm → Type)}  : ((∀ (x1 x2 : PointedPlusMagmaTerm) , ((P x1) → ((P x2) → (P (plusL x1 x2))))) → ((P eL) → (∀ (x : PointedPlusMagmaTerm) , (P x)))) 
  | pplusl pel (plusL x1 x2) := (pplusl _ _ (inductionB pplusl pel x1) (inductionB pplusl pel x2))  
  | pplusl pel eL := pel  
  def inductionCl   {A : Type} {P : ((ClPointedPlusMagmaTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClPointedPlusMagmaTerm A)) , ((P x1) → ((P x2) → (P (plusCl x1 x2))))) → ((P eCl) → (∀ (x : (ClPointedPlusMagmaTerm A)) , (P x))))) 
  | psing ppluscl pecl (sing x1) := (psing x1)  
  | psing ppluscl pecl (plusCl x1 x2) := (ppluscl _ _ (inductionCl psing ppluscl pecl x1) (inductionCl psing ppluscl pecl x2))  
  | psing ppluscl pecl eCl := pecl  
  def inductionOpB   {n : ℕ} {P : ((OpPointedPlusMagmaTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpPointedPlusMagmaTerm n)) , ((P x1) → ((P x2) → (P (plusOL x1 x2))))) → ((P eOL) → (∀ (x : (OpPointedPlusMagmaTerm n)) , (P x))))) 
  | pv pplusol peol (v x1) := (pv x1)  
  | pv pplusol peol (plusOL x1 x2) := (pplusol _ _ (inductionOpB pv pplusol peol x1) (inductionOpB pv pplusol peol x2))  
  | pv pplusol peol eOL := peol  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpPointedPlusMagmaTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpPointedPlusMagmaTerm2 n A)) , ((P x1) → ((P x2) → (P (plusOL2 x1 x2))))) → ((P eOL2) → (∀ (x : (OpPointedPlusMagmaTerm2 n A)) , (P x)))))) 
  | pv2 psing2 pplusol2 peol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pplusol2 peol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pplusol2 peol2 (plusOL2 x1 x2) := (pplusol2 _ _ (inductionOp pv2 psing2 pplusol2 peol2 x1) (inductionOp pv2 psing2 pplusol2 peol2 x2))  
  | pv2 psing2 pplusol2 peol2 eOL2 := peol2  
  def stageB  : (PointedPlusMagmaTerm → (Staged PointedPlusMagmaTerm))
  | (plusL x1 x2) := (stage2 plusL (codeLift2 plusL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  def stageCl   {A : Type}  : ((ClPointedPlusMagmaTerm A) → (Staged (ClPointedPlusMagmaTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (plusCl x1 x2) := (stage2 plusCl (codeLift2 plusCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  def stageOpB   {n : ℕ}  : ((OpPointedPlusMagmaTerm n) → (Staged (OpPointedPlusMagmaTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (plusOL x1 x2) := (stage2 plusOL (codeLift2 plusOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  def stageOp   {n : ℕ} {A : Type}  : ((OpPointedPlusMagmaTerm2 n A) → (Staged (OpPointedPlusMagmaTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (plusOL2 x1 x2) := (stage2 plusOL2 (codeLift2 plusOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (plusT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A)) 
  
end PointedPlusMagma