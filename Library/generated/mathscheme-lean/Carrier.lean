import init.data.nat.basic
import init.data.fin.basic
import data.vector
import .Prelude
open Staged
open nat
open fin
open vector
section Carrier   
  structure Carrier  (A : Type) : Type  
    
  open Carrier
  structure Sig  (AS : Type) : Type  
    
  structure Product  (A : Type) : Type  
    
  structure Hom  {A1 : Type} {A2 : Type} (Ca1 : (Carrier A1)) (Ca2 : (Carrier A2)) : Type := 
       (hom : (A1 → A2)) 
  
  structure RelInterp  {A1 : Type} {A2 : Type} (Ca1 : (Carrier A1)) (Ca2 : (Carrier A2)) : Type 1 := 
       (interp : (A1 → (A2 → Type))) 
  
  inductive CarrierTerm   : Type  
      
      open CarrierTerm 
  
  inductive ClCarrierTerm  (A : Type) : Type  
     | sing : (A → ClCarrierTerm)  
      open ClCarrierTerm 
  
  inductive OpCarrierTerm  (n : ℕ) : Type  
     | v : ((fin n) → OpCarrierTerm)  
      open OpCarrierTerm 
  
  inductive OpCarrierTerm2  (n : ℕ) (A : Type) : Type  
     | v2 : ((fin n) → OpCarrierTerm2) 
     | sing2 : (A → OpCarrierTerm2)  
      open OpCarrierTerm2 
  
  def simplifyCl   {A : Type}  : ((ClCarrierTerm A) → (ClCarrierTerm A)) 
  | (sing x1) := (sing x1)  
  def simplifyOpB   {n : ℕ}  : ((OpCarrierTerm n) → (OpCarrierTerm n)) 
  | (v x1) := (v x1)  
  def simplifyOp   {n : ℕ} {A : Type}  : ((OpCarrierTerm2 n A) → (OpCarrierTerm2 n A)) 
  | (v2 x1) := (v2 x1)  
  | (sing2 x1) := (sing2 x1)  
  def evalCl   {A : Type}  : ((Carrier A) → ((ClCarrierTerm A) → A)) 
  | Ca (sing x1) := x1  
  def evalOpB   {A : Type} {n : ℕ}  : ((Carrier A) → ((vector A n) → ((OpCarrierTerm n) → A))) 
  | Ca vars (v x1) := (nth vars x1)  
  def evalOp   {A : Type} {n : ℕ}  : ((Carrier A) → ((vector A n) → ((OpCarrierTerm2 n A) → A))) 
  | Ca vars (v2 x1) := (nth vars x1)  
  | Ca vars (sing2 x1) := x1  
  def inductionCl   {A : Type} {P : ((ClCarrierTerm A) → Type)}  : ((∀ (x1 : A) , (P (sing x1))) → (∀ (x : (ClCarrierTerm A)) , (P x))) 
  | psing (sing x1) := (psing x1)  
  def inductionOpB   {n : ℕ} {P : ((OpCarrierTerm n) → Type)}  : ((∀ (fin : (fin n)) , (P (v fin))) → (∀ (x : (OpCarrierTerm n)) , (P x))) 
  | pv (v x1) := (pv x1)  
  def inductionOp   {n : ℕ} {A : Type} {P : ((OpCarrierTerm2 n A) → Type)}  : ((∀ (fin : (fin n)) , (P (v2 fin))) → ((∀ (x1 : A) , (P (sing2 x1))) → (∀ (x : (OpCarrierTerm2 n A)) , (P x)))) 
  | pv2 psing2 (v2 x1) := (pv2 x1)  
  | pv2 psing2 (sing2 x1) := (psing2 x1)  
  def stageCl   {A : Type}  : ((ClCarrierTerm A) → (Staged (ClCarrierTerm A))) 
  | (sing x1) := (Now (sing x1))  
  def stageOpB   {n : ℕ}  : ((OpCarrierTerm n) → (Staged (OpCarrierTerm n))) 
  | (v x1) := (const (code (v x1)))  
  def stageOp   {n : ℕ} {A : Type}  : ((OpCarrierTerm2 n A) → (Staged (OpCarrierTerm2 n A))) 
  | (sing2 x1) := (Now (sing2 x1))  
  | (v2 x1) := (const (code (v2 x1)))  
  structure StagedRepr  (A : Type) (Repr : (Type → Type)) : Type  
    
end Carrier