module Carrier  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Carrier (A  : Set )  : Set where
    constructor CarrierC
  
  open Carrier
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
  
  record Hom (A1 A2  : Set ) (Ca1  : (Carrier A1 )) (Ca2  : (Carrier A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
  record RelInterp (A1 A2  : Set ) (Ca1  : (Carrier A1 )) (Ca2  : (Carrier A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
  data CarrierTerm  : Set where
    
  data ClCarrierTerm (A  : Set )  : Set where
    sing : (A  → (ClCarrierTerm A ) )
  data OpCarrierTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCarrierTerm n ) )
  data OpCarrierTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCarrierTerm2 n A ) )
    sing2 : (A  → (OpCarrierTerm2 n A ) )
  evalCl : ({A  : Set }  → ((Carrier A ) → ((ClCarrierTerm A ) → A )))
  evalCl Ca (sing x1 )  = x1 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Carrier A ) → ((Vec A n ) → ((OpCarrierTerm n ) → A ))))
  evalOp n Ca vars (v x1 )  = (lookup vars x1 )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Carrier A ) → ((Vec A n ) → ((OpCarrierTerm2 n A ) → A ))))
  evalOpE n Ca vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ca vars (sing2 x1 )  = x1 
  
  inductionCl : ((A  : Set ) (P  : ((ClCarrierTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((x  : (ClCarrierTerm A ))  → (P x ))))
  inductionCl _ p psing (sing x1 )  = (psing x1 )
  
  inductionOp : ((n  : Nat) (P  : ((OpCarrierTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((x  : (OpCarrierTerm n ))  → (P x ))))
  inductionOp _ p pv (v x1 )  = (pv x1 )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCarrierTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((x  : (OpCarrierTerm2 n A ))  → (P x )))))
  inductionOpE _ _ p pv2 psing2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 (sing2 x1 )  = (psing2 x1 )
  
  stageCl : ((A  : Set )  → ((ClCarrierTerm A ) → (Staged (ClCarrierTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageOp : ((n  : Nat)  → ((OpCarrierTerm n ) → (Staged (OpCarrierTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCarrierTerm2 n A ) → (Staged (OpCarrierTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
  