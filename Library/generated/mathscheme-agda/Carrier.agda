
module Carrier   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Carrier  (A : Set) : Set where 
    
  open Carrier
  record Sig  (AS : Set) : Set where 
    
  record Product  (A : Set) : Set where 
    
  record Hom  {A1 : Set} {A2 : Set} (Ca1 : (Carrier A1)) (Ca2 : (Carrier A2)) : Set where 
     field  
      hom : (A1 → A2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ca1 : (Carrier A1)) (Ca2 : (Carrier A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set))  
  
  data CarrierTerm   : Set where 
      
      
  data ClCarrierTerm  (A : Set) : Set where 
      sing : (A → (ClCarrierTerm A))  
      
  data OpCarrierTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCarrierTerm n))  
      
  data OpCarrierTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCarrierTerm2 n A)) 
      sing2 : (A → (OpCarrierTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClCarrierTerm A) → (ClCarrierTerm A)) 
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpCarrierTerm n) → (OpCarrierTerm n)) 
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpCarrierTerm2 n A) → (OpCarrierTerm2 n A)) 
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalCl :  {A : Set} →  ((Carrier A) → ((ClCarrierTerm A) → A)) 
  evalCl Ca (sing x1) = x1  
  evalOpB :  {A : Set} (n : Nat) →  ((Carrier A) → ((Vec A n) → ((OpCarrierTerm n) → A))) 
  evalOpB n Ca vars (v x1) = (lookup vars x1)  
  evalOp :  {A : Set} (n : Nat) →  ((Carrier A) → ((Vec A n) → ((OpCarrierTerm2 n A) → A))) 
  evalOp n Ca vars (v2 x1) = (lookup vars x1)  
  evalOp n Ca vars (sing2 x1) = x1  
  inductionCl :  (A : Set) (P : ((ClCarrierTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → ( (x : (ClCarrierTerm A)) → (P x))) 
  inductionCl _ p psing (sing x1) = (psing x1)  
  inductionOpB :  (n : Nat) (P : ((OpCarrierTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → ( (x : (OpCarrierTerm n)) → (P x))) 
  inductionOpB _ p pv (v x1) = (pv x1)  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpCarrierTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ( (x : (OpCarrierTerm2 n A)) → (P x)))) 
  inductionOp _ _ p pv2 psing2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 (sing2 x1) = (psing2 x1)  
  stageCl :  (A : Set) →  ((ClCarrierTerm A) → (Staged (ClCarrierTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageOpB :  (n : Nat) →  ((OpCarrierTerm n) → (Staged (OpCarrierTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOp :  (n : Nat) (A : Set) →  ((OpCarrierTerm2 n A) → (Staged (OpCarrierTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
    
 