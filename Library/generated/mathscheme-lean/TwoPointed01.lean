import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section TwoPointed01   
  structure TwoPointed01  (A : Type) : Type := 
       (e1 : A)
       (e2 : A) 
  
  open TwoPointed01
  structure Sig  (AS : Type) : Type := 
       (e1S : AS)
       (e2S : AS) 
  
  structure Product  (A : Type) : Type := 
       (e1P : (Prod A A))
       (e2P : (Prod A A)) 
  
  structure Hom  {A1 : Type} {A2 : Type} (Tw1 : (TwoPointed01 A1)) (Tw2 : (TwoPointed01 A2)) : Type := 
       (hom : (A1 → A2))
       (pres_e1 : (hom (e1 Tw1)) = (e1 Tw2))
       (pres_e2 : (hom (e2 Tw1)) = (e2 Tw2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Tw1 : (TwoPointed01 A1)) (Tw2 : (TwoPointed01 A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type)))
       (interp_e1 : (interp (e1 Tw1) (e1 Tw2)))
       (interp_e2 : (interp (e2 Tw1) (e2 Tw2))) 
  
  inductive TwoPointed01Term   : Type  
     | e1L : TwoPointed01Term 
     | e2L : TwoPointed01Term  
      open TwoPointed01Term 
  
  inductive ClTwoPointed01Term  (A : Type) : Type  
     | sing : (A → ClTwoPointed01Term) 
     | e1Cl : ClTwoPointed01Term 
     | e2Cl : ClTwoPointed01Term  
      open ClTwoPointed01Term 
  
  inductive OpTwoPointed01Term  (n : ℕ) : Type  
     | v : ((fin n) → OpTwoPointed01Term) 
     | e1OL : OpTwoPointed01Term 
     | e2OL : OpTwoPointed01Term  
      open OpTwoPointed01Term 
  
  inductive OpTwoPointed01Term2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpTwoPointed01Term2) 
     | sing2 : (A → OpTwoPointed01Term2) 
     | e1OL2 : OpTwoPointed01Term2 
     | e2OL2 : OpTwoPointed01Term2  
      open OpTwoPointed01Term2 
  
  def simplifyCl   (A : Type)  : ((ClTwoPointed01Term A) → (ClTwoPointed01Term A)) 
  | e1Cl := e1Cl  
  | e2Cl := e2Cl  
  | (sing x1) := (sing x1)  
  def simplifyOpB   (n : ℕ)  : ((OpTwoPointed01Term n) → (OpTwoPointed01Term n)) 
  | e1OL := e1OL  
  | e2OL := e2OL  
  | (v x1) := (v x1)  
  def simplifyOp   (n : ℕ) (A : Type)  : ((OpTwoPointed01Term2 n A) → (OpTwoPointed01Term2 n A)) 
  | e1OL2 := e1OL2  
  | e2OL2 := e2OL2  
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalB   {A : Type}  : ((TwoPointed01 A) → (TwoPointed01Term → A)) 
  | Tw e1L := (e1 Tw)  
  | Tw e2L := (e2 Tw)  
  def evalCl   {A : Type}  : ((TwoPointed01 A) → ((ClTwoPointed01Term A) → A)) 
  | Tw (sing x1) := x1  
  | Tw e1Cl := (e1 Tw)  
  | Tw e2Cl := (e2 Tw)  
  def evalOpB   {A : Type} (n : ℕ)  : ((TwoPointed01 A) → ((vector A n) → ((OpTwoPointed01Term n) → A))) 
  | Tw vars (v x1) := (nth vars x1)  
  | Tw vars e1OL := (e1 Tw)  
  | Tw vars e2OL := (e2 Tw)  
  def evalOp   {A : Type} (n : ℕ)  : ((TwoPointed01 A) → ((vector A n) → ((OpTwoPointed01Term2 n A) → A))) 
  | Tw vars (v2 x1) := (nth vars x1)  
  | Tw vars (sing2 x1) := x1  
  | Tw vars e1OL2 := (e1 Tw)  
  | Tw vars e2OL2 := (e2 Tw)  
  def inductionB   (P : (TwoPointed01Term → Type))  : ((P e1L) → ((P e2L) → (∀ (x : TwoPointed01Term) , (P x)))) 
  | pe1l pe2l e1L := pe1l  
  | pe1l pe2l e2L := pe2l  
  def inductionCl   (A : Type) (P : ((ClTwoPointed01Term A) → Type))  : ((∀ (x1 : A) , (P (sing x1))) → ((P e1Cl) → ((P e2Cl) → (∀ (x : (ClTwoPointed01Term A)) , (P x))))) 
  | psing pe1cl pe2cl (sing x1) := (psing x1)  
  | psing pe1cl pe2cl e1Cl := pe1cl  
  | psing pe1cl pe2cl e2Cl := pe2cl  
  def inductionOpB   (n : ℕ) (P : ((OpTwoPointed01Term n) → Type))  : ((∀ (fin : (fin n)) , (P (v fin))) → ((P e1OL) → ((P e2OL) → (∀ (x : (OpTwoPointed01Term n)) , (P x))))) 
  | pv pe1ol pe2ol (v x1) := (pv x1)  
  | pv pe1ol pe2ol e1OL := pe1ol  
  | pv pe1ol pe2ol e2OL := pe2ol  
  def inductionOp   (n : ℕ) (A : Type) (P : ((OpTwoPointed01Term2 n A) → Type))  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → ((P e1OL2) → ((P e2OL2) → (∀ (x : (OpTwoPointed01Term2 n A)) , (P x)))))) 
  | pv2 psing2 pe1ol2 pe2ol2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 pe1ol2 pe2ol2 (sing2 x1) := (psing2 x1)  
  | pv2 psing2 pe1ol2 pe2ol2 e1OL2 := pe1ol2  
  | pv2 psing2 pe1ol2 pe2ol2 e2OL2 := pe2ol2  
  def stageB  : (TwoPointed01Term → (Staged TwoPointed01Term))
  | e1L := (Now e1L)  
  | e2L := (Now e2L)  
  def stageCl   (A : Type)  : ((ClTwoPointed01Term A) → (Staged (ClTwoPointed01Term A))) 
  | (sing x1) := (Now (sing x1))  
  | e1Cl := (Now e1Cl)  
  | e2Cl := (Now e2Cl)  
  def stageOpB   (n : ℕ)  : ((OpTwoPointed01Term n) → (Staged (OpTwoPointed01Term n))) 
  | (v x1) := (const (code (v x1)))  
  | e1OL := (Now e1OL)  
  | e2OL := (Now e2OL)  
  def stageOp   (n : ℕ) (A : Type)  : ((OpTwoPointed01Term2 n A) → (Staged (OpTwoPointed01Term2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  | e1OL2 := (Now e1OL2)  
  | e2OL2 := (Now e2OL2)  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type := 
       (e1T : (Repr A))
       (e2T : (Repr A)) 
  
end TwoPointed01