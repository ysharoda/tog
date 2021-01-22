import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section LeftLoop   
  structure LeftLoop  (A : Type) : Type := 
       (op : (A → (A → A)))
       (e : A)
       (runit_e : (∀ {x : A} , (op x e) = x))
       (linv : (A → (A → A)))
       (leftCancel : (∀ {x y : A} , (op x (linv x y)) = y))
       (lefCancelOp : (∀ {x y : A} , (linv x (op x y)) = y)) 
  
  open LeftLoop
  structure Sig  (AS : Type) : Type := 
       (opS : (AS → (AS → AS)))
       (eS : AS)
       (linvS : (AS → (AS → AS))) 
  
  structure Product  (A : Type) : Type := 
       (opP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (eP : (Prod A A))
       (linvP : ((Prod A A) → ((Prod A A) → (Prod A A))))
       (runit_eP : (∀ {xP : (Prod A A)} , (opP xP eP) = xP))
       (leftCancelP : (∀ {xP yP : (Prod A A)} , (opP xP (linvP xP yP)) = yP))
       (lefCancelOpP : (∀ {xP yP : (Prod A A)} , (linvP xP (opP xP yP)) = yP)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Le1 : (LeftLoop A1)) (Le2 : (LeftLoop A2)) : Type := 
       (hom : (A1 → A2))
       (pres_op : (∀ {x1 x2 : A1} , (hom ((op Le1) x1 x2)) = ((op Le2) (hom x1) (hom x2))))
       (pres_e : (hom (e Le1)) = (e Le2))
       (pres_linv : (∀ {x1 x2 : A1} , (hom ((linv Le1) x1 x2)) = ((linv Le2) (hom x1) (hom x2)))) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Le1 : (LeftLoop A1)) (Le2 : (LeftLoop A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_op : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((op Le1) x1 x2) ((op Le2) y1 y2))))))
       (interp_e : (interp (e Le1) (e Le2)))
       (interp_linv : (∀ {x1 x2 : A1} {y1 y2 : A2} , ((interp x1 y1) → ((interp x2 y2) → (interp ((linv Le1) x1 x2) ((linv Le2) y1 y2)))))) 
  
  inductive LeftLoopLTerm   : Type  
     | opL : (LeftLoopLTerm → (LeftLoopLTerm → LeftLoopLTerm)) 
     | eL : LeftLoopLTerm 
     | linvL : (LeftLoopLTerm → (LeftLoopLTerm → LeftLoopLTerm))  
      open LeftLoopLTerm 
  
  inductive ClLeftLoopClTerm  (A : Type) : Type  
     | sing : (A → ClLeftLoopClTerm) 
     | opCl : (ClLeftLoopClTerm → (ClLeftLoopClTerm → ClLeftLoopClTerm)) 
     | eCl : ClLeftLoopClTerm 
     | linvCl : (ClLeftLoopClTerm → (ClLeftLoopClTerm → ClLeftLoopClTerm))  
      open ClLeftLoopClTerm 
  
  inductive OpLeftLoopOLTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpLeftLoopOLTerm) 
     | opOL : (OpLeftLoopOLTerm → (OpLeftLoopOLTerm → OpLeftLoopOLTerm)) 
     | eOL : OpLeftLoopOLTerm 
     | linvOL : (OpLeftLoopOLTerm → (OpLeftLoopOLTerm → OpLeftLoopOLTerm))  
      open OpLeftLoopOLTerm 
  
  inductive OpLeftLoopOL2Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpLeftLoopOL2Term2) 
     | sing2 : (A → OpLeftLoopOL2Term2) 
     | opOL2 : (OpLeftLoopOL2Term2 → (OpLeftLoopOL2Term2 → OpLeftLoopOL2Term2)) 
     | eOL2 : OpLeftLoopOL2Term2 
     | linvOL2 : (OpLeftLoopOL2Term2 → (OpLeftLoopOL2Term2 → OpLeftLoopOL2Term2))  
      open OpLeftLoopOL2Term2 
  
  def simplifyCl   {A : Type}  : ((ClLeftLoopClTerm A) → (ClLeftLoopClTerm A)) 
  | (opCl x eCl) := x  
  | (opCl x1 x2) := (opCl (simplifyCl x1) (simplifyCl x2))  
  | eCl := eCl  
  | (linvCl x1 x2) := (linvCl (simplifyCl x1) (simplifyCl x2))  
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpLeftLoopOLTerm n) → (OpLeftLoopOLTerm n)) 
  | (opOL x eOL) := x  
  | (opOL x1 x2) := (opOL (simplifyOpB x1) (simplifyOpB x2))  
  | eOL := eOL  
  | (linvOL x1 x2) := (linvOL (simplifyOpB x1) (simplifyOpB x2))  
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpLeftLoopOL2Term2 n A) → (OpLeftLoopOL2Term2 n A)) 
  | (opOL2 x eOL2) := x  
  | (opOL2 x1 x2) := (opOL2 (simplifyOp x1) (simplifyOp x2))  
  | eOL2 := eOL2  
  | (linvOL2 x1 x2) := (linvOL2 (simplifyOp x1) (simplifyOp x2))  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((LeftLoop A) → (LeftLoopLTerm → A)) 
  | Le (opL x1 x2) := ((op Le) (evalB Le x1) (evalB Le x2))  
  | Le eL := (e Le)  
  | Le (linvL x1 x2) := ((linv Le) (evalB Le x1) (evalB Le x2))  
  def evalCl   {A : Type}  : ((LeftLoop A) → ((ClLeftLoopClTerm A) → A)) 
  | Le (sing x1) := x1  
  | Le (opCl x1 x2) := ((op Le) (evalCl Le x1) (evalCl Le x2))  
  | Le eCl := (e Le)  
  | Le (linvCl x1 x2) := ((linv Le) (evalCl Le x1) (evalCl Le x2))  
  def evalOpB   {A : Type} {n : ℕ}  : ((LeftLoop A) → ((vector A n) → ((OpLeftLoopOLTerm n) → A))) 
  | Le vars (v x1) := (nth vars x1)  
  | Le vars (opOL x1 x2) := ((op Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  | Le vars eOL := (e Le)  
  | Le vars (linvOL x1 x2) := ((linv Le) (evalOpB Le vars x1) (evalOpB Le vars x2))  
  def evalOp   {A : Type} {n : ℕ}  : ((LeftLoop A) → ((vector A n) → ((OpLeftLoopOL2Term2 n A) → A))) 
  | Le vars (v2 x1) := (nth vars x1)  
  | Le vars (sing2 x1) := x1  
  | Le vars (opOL2 x1 x2) := ((op Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  | Le vars eOL2 := (e Le)  
  | Le vars (linvOL2 x1 x2) := ((linv Le) (evalOp Le vars x1) (evalOp Le vars x2))  
  def inductionB   {P : (LeftLoopLTerm → Type)}  : ((∀ (x1 x2 : LeftLoopLTerm) , ((P x1) → ((P x2) → (P (opL x1 x2))))) → ((P eL) → ((∀ (x1 x2 : LeftLoopLTerm) , ((P x1) → ((P x2) → (P (linvL x1 x2))))) → (∀ (x : LeftLoopLTerm) , (P x))))) 
  | popl pel plinvl (opL x1 x2) := (popl _ _ (inductionB popl pel plinvl x1) (inductionB popl pel plinvl x2))  
  | popl pel plinvl eL := pel  
  | popl pel plinvl (linvL x1 x2) := (plinvl _ _ (inductionB popl pel plinvl x1) (inductionB popl pel plinvl x2))  
  def inductionCl   {A : Type} {P : ((ClLeftLoopClTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → ((∀ (x1 x2 : (ClLeftLoopClTerm A)) , ((P x1) → ((P x2) → (P (opCl x1 x2))))) → ((P eCl) → ((∀ (x1 x2 : (ClLeftLoopClTerm A)) , ((P x1) → ((P x2) → (P (linvCl x1 x2))))) → (∀ (x : (ClLeftLoopClTerm A)) , (P x)))))) 
  | psing popcl pecl plinvcl (sing x1) := (psing x1)  
  | psing popcl pecl plinvcl (opCl x1 x2) := (popcl _ _ (inductionCl psing popcl pecl plinvcl x1) (inductionCl psing popcl pecl plinvcl x2))  
  | psing popcl pecl plinvcl eCl := pecl  
  | psing popcl pecl plinvcl (linvCl x1 x2) := (plinvcl _ _ (inductionCl psing popcl pecl plinvcl x1) (inductionCl psing popcl pecl plinvcl x2))  
  def inductionOpB   {n : ℕ} {P : ((OpLeftLoopOLTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → ((∀ (x1 x2 : (OpLeftLoopOLTerm n)) , ((P x1) → ((P x2) → (P (opOL x1 x2))))) → ((P eOL) → ((∀ (x1 x2 : (OpLeftLoopOLTerm n)) , ((P x1) → ((P x2) → (P (linvOL x1 x2))))) → (∀ (x : (OpLeftLoopOLTerm n)) , (P x)))))) 
  | pv popol peol plinvol (v x1) := (pv x1)  
  | pv popol peol plinvol (opOL x1 x2) := (popol _ _ (inductionOpB pv popol peol plinvol x1) (inductionOpB pv popol peol plinvol x2))  
  | pv popol peol plinvol eOL := peol  
  | pv popol peol plinvol (linvOL x1 x2) := (plinvol _ _ (inductionOpB pv popol peol plinvol x1) (inductionOpB pv popol peol plinvol x2))  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpLeftLoopOL2Term2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((∀ (x1 x2 : (OpLeftLoopOL2Term2 n A)) , ((P x1) → ((P x2) → (P (opOL2 x1 x2))))) → ((P eOL2) → ((∀ (x1 x2 : (OpLeftLoopOL2Term2 n A)) , ((P x1) → ((P x2) → (P (linvOL2 x1 x2))))) → (∀ (x : (OpLeftLoopOL2Term2 n A)) , (P x))))))) 
  | pv2 psing2 popol2 peol2 plinvol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 popol2 peol2 plinvol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 popol2 peol2 plinvol2 (opOL2 x1 x2) := (popol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 x2))  
  | pv2 psing2 popol2 peol2 plinvol2 eOL2 := peol2  
  | pv2 psing2 popol2 peol2 plinvol2 (linvOL2 x1 x2) := (plinvol2 _ _ (inductionOp pv2 psing2 popol2 peol2 plinvol2 x1) (inductionOp pv2 psing2 popol2 peol2 plinvol2 x2))  
  def stageB  : (LeftLoopLTerm → (Staged LeftLoopLTerm))
  | (opL x1 x2) := (stage2 opL (codeLift2 opL) (stageB x1) (stageB x2))  
  | eL := (Now eL)  
  | (linvL x1 x2) := (stage2 linvL (codeLift2 linvL) (stageB x1) (stageB x2))  
  def stageCl   {A : Type}  : ((ClLeftLoopClTerm A) → (Staged (ClLeftLoopClTerm A))) 
  | (sing x1) := (Now (sing x1))  
  | (opCl x1 x2) := (stage2 opCl (codeLift2 opCl) (stageCl x1) (stageCl x2))  
  | eCl := (Now eCl)  
  | (linvCl x1 x2) := (stage2 linvCl (codeLift2 linvCl) (stageCl x1) (stageCl x2))  
  def stageOpB   {n : ℕ}  : ((OpLeftLoopOLTerm n) → (Staged (OpLeftLoopOLTerm n))) 
  | (v x1) := (const (code (v x1)))  
  | (opOL x1 x2) := (stage2 opOL (codeLift2 opOL) (stageOpB x1) (stageOpB x2))  
  | eOL := (Now eOL)  
  | (linvOL x1 x2) := (stage2 linvOL (codeLift2 linvOL) (stageOpB x1) (stageOpB x2))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpLeftLoopOL2Term2 n A) → (Staged (OpLeftLoopOL2Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | (opOL2 x1 x2) := (stage2 opOL2 (codeLift2 opOL2) (stageOp x1) (stageOp x2))  
  | eOL2 := (Now eOL2)  
  | (linvOL2 x1 x2) := (stage2 linvOL2 (codeLift2 linvOL2) (stageOp x1) (stageOp x2))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (opT : ((Repr A) → ((Repr A) → (Repr A))))
       (eT : (Repr A))
       (linvT : ((Repr A) → ((Repr A) → (Repr A)))) 
  
end LeftLoop