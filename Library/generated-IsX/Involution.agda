
 module Involution  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolution (A  : Set ) (prim  : (A  → A ))  : Set where
    constructor IsInvolutionC
    field
      involutive_prim : ({x  : A }  → (prim (prim x ) ) ≡ x ) 
  
  record Involution (A  : Set )  : Set where
    constructor InvolutionC
    field
      prim : (A  → A )
      isInvolution : (IsInvolution A prim ) 
  
  open Involution
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      involutive_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (In1  : (Involution A1 )) (In2  : (Involution A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (Involution A1 )) (In2  : (Involution A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) ))) 
  
  data InvolutionTerm  : Set where
    primL : (InvolutionTerm   → InvolutionTerm  ) 
  
  data ClInvolutionTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutionTerm A ) )
    primCl : ((ClInvolutionTerm A )  → (ClInvolutionTerm A ) ) 
  
  data OpInvolutionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutionTerm n ) )
    primOL : ((OpInvolutionTerm n )  → (OpInvolutionTerm n ) ) 
  
  data OpInvolutionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutionTerm2 n A ) )
    sing2 : (A  → (OpInvolutionTerm2 n A ) )
    primOL2 : ((OpInvolutionTerm2 n A )  → (OpInvolutionTerm2 n A ) ) 
  
  simplifyB : (InvolutionTerm  → InvolutionTerm )
  simplifyB (primL (primL x ) )  = x 
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInvolutionTerm A ) → (ClInvolutionTerm A )))
  simplifyCl _ (primCl (primCl x ) )  = x 
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutionTerm n ) → (OpInvolutionTerm n )))
  simplifyOp _ (primOL (primOL x ) )  = x 
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutionTerm2 n A ) → (OpInvolutionTerm2 n A )))
  simplifyOpE _ _ (primOL2 (primOL2 x ) )  = x 
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Involution A ) → (InvolutionTerm  → A )))
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((Involution A ) → ((ClInvolutionTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Involution A ) → ((Vec A n ) → ((OpInvolutionTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Involution A ) → ((Vec A n ) → ((OpInvolutionTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InvolutionTerm  → Set ))  → (((x1  : InvolutionTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : InvolutionTerm )  → (P x ))))
  inductionB p ppriml (primL x1 )  = (ppriml _ (inductionB p ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInvolutionTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClInvolutionTerm A ))  → (P x )))))
  inductionCl _ p psing pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInvolutionTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpInvolutionTerm n ))  → (P x )))))
  inductionOp _ p pv pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInvolutionTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpInvolutionTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 x1 ) )
  
  primL' : (  (InvolutionTerm   → InvolutionTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (InvolutionTerm  → (Staged InvolutionTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  primCl' : ({A  : Set }  → ((ClInvolutionTerm A )  → (ClInvolutionTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInvolutionTerm A ) → (Staged (ClInvolutionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  primOL' : ({n  : Nat}  → ((OpInvolutionTerm n )  → (OpInvolutionTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutionTerm n ) → (Staged (OpInvolutionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutionTerm2 n A )  → (OpInvolutionTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutionTerm2 n A ) → (Staged (OpInvolutionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) ) 
   
