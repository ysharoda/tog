import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftInverse   
  structure LeftInverse  (A : Type) : Type := 
       (inv : (A → A))
       (e : A)
       (op : (A → (A → A)))
       (leftInverse_inv_op_e : (∀ {x : A} , (op x (inv x)) = e)) 
  
  open LeftInverse
  structure Sig  (AS : Type) : Type := 
       (invS : (AS → AS))
       (eS : AS)
       (opS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (invP : ((Prod A A) → (Prod A A)))
       (eP : (Prod A A))
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (leftInverse_inv_op_eP : (∀ {xP : (Prod A A)} , (opP xP (invP xP)) = eP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftInverse A1)) (Le2 : (LeftInverse A2)) : Type := 
       (hom : (A1 → A2))
       (pres_inv : (∀ {x1 : A1} , (hom ((inv Le1) x1)) = ((inv Le2) (hom x1))))
       (pres_e : (hom (e Le1)) = (e Le2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Le1) x1 x2)) = ((op Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftInverse A1)) (Le2 : (LeftInverse A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_inv : (∀ {x1 : A1} {y1 : A2} , ((interp x1 y1) → (interp ((inv Le1) x1) ((inv Le2) y1)))))
       (interp_e : (interp (e Le1) (e Le2)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2)))))) 
  
  inductive LeftInverseLTerm   : Type  
     | invL : (LeftInverseLTerm → LeftInverseLTerm) 
     | eL : LeftInverseLTerm 
     | opL : (LeftInverseLTerm → (LeftInverseLTerm → LeftInverseLTerm))  
      open LeftInverseLTerm 
  
  inductive ClLeftInverseClTerm  (A : Type) : Type  
     | sing : (A → ClLeftInverseClTerm) 
     | invCl : (ClLeftInverseClTerm → ClLeftInverseClTerm) 
     | eCl : ClLeftInverseClTerm 
     | opCl : (ClLeftInverseClTerm → (ClLeftInverseClTerm → ClLeftInverseClTerm))  
      open ClLeftInverseClTerm 
  
  inductive OpLeftInverseOLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftInverseOLTerm) 
     | invOL : (OpLeftInverseOLTerm → OpLeftInverseOLTerm) 
     | eOL : OpLeftInverseOLTerm 
     | opOL : (OpLeftInverseOLTerm → (OpLeftInverseOLTerm → OpLeftInverseOLTerm))  
      open OpLeftInverseOLTerm 
  
  inductive OpLeftInverseOL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftInverseOL2Term2) 
     | sing2 : (A → OpLeftInverseOL2Term2) 
     | invOL2 : (OpLeftInverseOL2Term2 → OpLeftInverseOL2Term2) 
     | eOL2 : OpLeftInverseOL2Term2 
     | opOL2 : (OpLeftInverseOL2Term2 → (OpLeftInverseOL2Term2 → OpLeftInverseOL2Term2))  
      open OpLeftInverseOL2Term2 
  
  def simplifyCl   (A : Type)  : ((ClLeftInverseClTerm A) → (ClLeftInverseClTerm A)) 
  | (invCl x1) := (invCl (simplifyCl x1))  
  | eCl := eCl  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpLeftInverseOLTerm n) → (OpLeftInverseOLTerm n)) 
  | (invOL x1) := (invOL (simplifyOpB x1))  
  | eOL := eOL  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpLeftInverseOL2Term2 n A) → (OpLeftInverseOL2Term2 n A)) 
  | (invOL2 x1) := (invOL2 (simplifyOp x1))  
  | eOL2 := eOL2  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftInverse A) → (LeftInverseLTerm → A)) 
  | Le (invL x1) := ((inv Le) (evalB Le x1))  
  | Le eL := (e Le)  
  | Le (opL x1 x2) := ((op Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftInverse A) → ((ClLeftInverseClTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (invCl x1) := ((inv Le) (evalCl Le x1))  
  | Le eCl := (e Le)  
  | Le (opCl x1 x2) := ((op Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} (n : ℕ)  : ((LeftInverse A) → ((vector A n) → ((OpLeftInverseOLTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (invOL x1) := ((inv Le) (evalOpB Le vars x1))  
  | Le vars eOL := (e Le)  
  | Le vars (opOL x1 x2) := ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} (n : ℕ)  : ((LeftInverse A) → ((vector A n) → ((OpLeftInverseOL2Term2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (invOL2 x1) := ((inv Le) (evalOp Le vars x1))  
  | Le vars eOL2 := (e Le)  
  | Le vars (opOL2 x1 x2) := ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   (P : (LeftInverseLTerm → Type))  : ((∀ (x1 : LeftInverseLTerm) , ((P x1) → (P (invL x1)))) → ((P eL) → ((∀ (x1 x2 : LeftInverseLTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → (∀ (x : LeftInverseLTerm) , (P x))))) 
  | pinvl pel popl (invL x1) := (pinvl _ (inductionB pinvl pel popl x1))  
  | pinvl pel popl eL := pel  
  | pinvl pel popl (opL x1 x2) := (popl _ _ (inductionB pinvl pel popl x1) (inductionB pinvl pel popl x2))  
  def inductionCl   (A : Type) (P : ((ClLeftInverseClTerm A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 : (ClLeftInverseClTerm A)) , ((P x1) → (P (invCl x1)))) → ((P eCl) → ((∀ (x1 x2 : (ClLeftInverseClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → (∀ (x : (ClLeftInverseClTerm A)) , (P x)))))) 
  | psing pinvcl pecl popcl (sing x1) := (psing x1)  
  | psing pinvcl pecl popcl (invCl x1) := (pinvcl _ (inductionCl psing pinvcl pecl popcl x1))  
  | psing pinvcl pecl popcl eCl := pecl  
  | psing pinvcl pecl popcl (opCl x1 x2) := (popcl _ _ (inductionCl psing pinvcl pecl popcl x1) (inductionCl psing pinvcl pecl popcl x2))  
  def inductionOpB   (n : ℕ) (P : ((OpLeftInverseOLTerm n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 : (OpLeftInverseOLTerm n)) , ((P x1) → (P (invOL x1)))) → ((P eOL) → ((∀ (x1 x2 : (OpLeftInverseOLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → (∀ (x : (OpLeftInverseOLTerm n)) , (P x)))))) 
  | pv pinvol peol popol (v x1) := (pv x1)  
  | pv pinvol peol popol (invOL x1) := (pinvol _ (inductionOpB pv pinvol peol popol x1))  
  | pv pinvol peol popol eOL := peol  
  | pv pinvol peol popol (opOL x1 x2) := (popol _ _ (inductionOpB pv pinvol peol popol x1) (inductionOpB pv pinvol peol popol x2))  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpLeftInverseOL2Term2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 : (OpLeftInverseOL2Term2 n A)) , ((P x1) → (P (invOL2 x1)))) → ((P eOL2) → ((∀ (x1 x2 : (OpLeftInverseOL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → (∀ (x : (OpLeftInverseOL2Term2 n A)) , (P x))))))) 
  | pv2 psing2 pinvol2 peol2 popol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pinvol2 peol2 popol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1) := (pinvol2 _ (inductionOp pv2 psing2 pinvol2 peol2 popol2 x1))  
  | pv2 psing2 pinvol2 peol2 popol2 eOL2 := peol2  
  | pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 pinvol2 peol2 popol2 x1) (inductionOp pv2 psing2 pinvol2 peol2 popol2 x2))  
  def stageB  : (LeftInverseLTerm → (Staged LeftInverseLTerm))
  | (invL x1) := (stage1 invL (codeLift1 invL) (stageB x1))  
  | eL := (Now eL)  
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  def stageCl   (A : Type)  : ((ClLeftInverseClTerm A) → (Staged (ClLeftInverseClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (invCl x1) := (stage1 invCl (codeLift1 invCl) (stageCl x1))  
  | eCl := (Now eCl)  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  def stageOpB   (n : ℕ)  : ((OpLeftInverseOLTerm n) → (Staged (OpLeftInverseOLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (invOL x1) := (stage1 invOL (codeLift1 invOL) (stageOpB x1))  
  | eOL := (Now eOL)  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   (n : ℕ) (A : Type)  : ((OpLeftInverseOL2Term2 n A) → (Staged (OpLeftInverseOL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (invOL2 x1) := (stage1 invOL2 (codeLift1 invOL2) (stageOp x1))  
  | eOL2 := (Now eOL2)  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (invT : ((Repr A) → (Repr A)))
       (eT : (Repr A))
       (opT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftInverse