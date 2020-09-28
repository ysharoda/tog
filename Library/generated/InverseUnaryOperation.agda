module InverseUnaryOperation  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InverseUnaryOperation (A  : Set )  : Set where
    constructor InverseUnaryOperationC
    field
      inv : (A  → A )
  open InverseUnaryOperation
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      invS : (AS  → AS )
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      invP : ((Prod AP AP ) → (Prod AP AP ))
  record Hom (A1 A2  : Set ) (In1  : (InverseUnaryOperation A1 )) (In2  : (InverseUnaryOperation A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-inv : ({x1  : A1}  → (hom ((inv In1 ) x1 ) ) ≡ ((inv In2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (In1  : (InverseUnaryOperation A1 )) (In2  : (InverseUnaryOperation A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv In1 ) x1 ) ((inv In2 ) y1 ) )))
  data InverseUnaryOperationTerm  : Set where
    invL : (InverseUnaryOperationTerm   → InverseUnaryOperationTerm  )
  data ClInverseUnaryOperationTerm (A  : Set )  : Set where
    sing : (A  → (ClInverseUnaryOperationTerm A ) )
    invCl : ((ClInverseUnaryOperationTerm A )  → (ClInverseUnaryOperationTerm A ) )
  data OpInverseUnaryOperationTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInverseUnaryOperationTerm n ) )
    invOL : ((OpInverseUnaryOperationTerm n )  → (OpInverseUnaryOperationTerm n ) )
  data OpInverseUnaryOperationTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInverseUnaryOperationTerm2 n A ) )
    sing2 : (A  → (OpInverseUnaryOperationTerm2 n A ) )
    invOL2 : ((OpInverseUnaryOperationTerm2 n A )  → (OpInverseUnaryOperationTerm2 n A ) )
  evalB : ({A  : Set }  → ((InverseUnaryOperation A ) → (InverseUnaryOperationTerm  → A )))
  evalB In (invL x1 )  = ((inv In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((InverseUnaryOperation A ) → ((ClInverseUnaryOperationTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (invCl x1 )  = ((inv In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InverseUnaryOperation A ) → ((Vec A n ) → ((OpInverseUnaryOperationTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (invOL x1 )  = ((inv In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InverseUnaryOperation A ) → ((Vec A n ) → ((OpInverseUnaryOperationTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (invOL2 x1 )  = ((inv In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InverseUnaryOperationTerm  → Set ))  → (((x1  : InverseUnaryOperationTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((x  : InverseUnaryOperationTerm )  → (P x ))))
  inductionB p pinvl (invL x1 )  = (pinvl _ (inductionB p pinvl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInverseUnaryOperationTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInverseUnaryOperationTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((x  : (ClInverseUnaryOperationTerm A ))  → (P x )))))
  inductionCl _ p psing pinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pinvcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing pinvcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInverseUnaryOperationTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInverseUnaryOperationTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((x  : (OpInverseUnaryOperationTerm n ))  → (P x )))))
  inductionOp _ p pv pinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pinvol (invOL x1 )  = (pinvol _ (inductionOp _ p pv pinvol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInverseUnaryOperationTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInverseUnaryOperationTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((x  : (OpInverseUnaryOperationTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 pinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 pinvol2 x1 ) )
  
  invL' : (  (InverseUnaryOperationTerm   → InverseUnaryOperationTerm  ))
  invL' x1  = (invL x1 )
  
  stageB : (InverseUnaryOperationTerm  → (Staged InverseUnaryOperationTerm  ))
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  invCl' : ({A  : Set }  → ((ClInverseUnaryOperationTerm A )  → (ClInverseUnaryOperationTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInverseUnaryOperationTerm A ) → (Staged (ClInverseUnaryOperationTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  invOL' : ({n  : Nat}  → ((OpInverseUnaryOperationTerm n )  → (OpInverseUnaryOperationTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInverseUnaryOperationTerm n ) → (Staged (OpInverseUnaryOperationTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpInverseUnaryOperationTerm2 n A )  → (OpInverseUnaryOperationTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInverseUnaryOperationTerm2 n A ) → (Staged (OpInverseUnaryOperationTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      invT : ((Repr A )  → (Repr A ) )