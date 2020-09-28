module InvolutiveMagmaSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveMagmaSig (A  : Set )  : Set where
    constructor InvolutiveMagmaSigC
    field
      prim : (A  → A )
      op : (A  → (A  → A ))
  open InvolutiveMagmaSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveMagmaSig A1 )) (In2  : (InvolutiveMagmaSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveMagmaSig A1 )) (In2  : (InvolutiveMagmaSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) ))))
  data InvolutiveMagmaSigTerm  : Set where
    primL : (InvolutiveMagmaSigTerm   → InvolutiveMagmaSigTerm  )
    opL : (InvolutiveMagmaSigTerm   → (InvolutiveMagmaSigTerm   → InvolutiveMagmaSigTerm  ))
  data ClInvolutiveMagmaSigTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveMagmaSigTerm A ) )
    primCl : ((ClInvolutiveMagmaSigTerm A )  → (ClInvolutiveMagmaSigTerm A ) )
    opCl : ((ClInvolutiveMagmaSigTerm A )  → ((ClInvolutiveMagmaSigTerm A )  → (ClInvolutiveMagmaSigTerm A ) ))
  data OpInvolutiveMagmaSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveMagmaSigTerm n ) )
    primOL : ((OpInvolutiveMagmaSigTerm n )  → (OpInvolutiveMagmaSigTerm n ) )
    opOL : ((OpInvolutiveMagmaSigTerm n )  → ((OpInvolutiveMagmaSigTerm n )  → (OpInvolutiveMagmaSigTerm n ) ))
  data OpInvolutiveMagmaSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveMagmaSigTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveMagmaSigTerm2 n A ) )
    primOL2 : ((OpInvolutiveMagmaSigTerm2 n A )  → (OpInvolutiveMagmaSigTerm2 n A ) )
    opOL2 : ((OpInvolutiveMagmaSigTerm2 n A )  → ((OpInvolutiveMagmaSigTerm2 n A )  → (OpInvolutiveMagmaSigTerm2 n A ) ))
  evalB : ({A  : Set }  → ((InvolutiveMagmaSig A ) → (InvolutiveMagmaSigTerm  → A )))
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveMagmaSig A ) → ((ClInvolutiveMagmaSigTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveMagmaSig A ) → ((Vec A n ) → ((OpInvolutiveMagmaSigTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveMagmaSig A ) → ((Vec A n ) → ((OpInvolutiveMagmaSigTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  inductionB : ((P  : (InvolutiveMagmaSigTerm  → Set ))  → (((x1  : InvolutiveMagmaSigTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : InvolutiveMagmaSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : InvolutiveMagmaSigTerm )  → (P x )))))
  inductionB p ppriml popl (primL x1 )  = (ppriml _ (inductionB p ppriml popl x1 ) )
  
  inductionB p ppriml popl (opL x1 x2 )  = (popl _ _ (inductionB p ppriml popl x1 ) (inductionB p ppriml popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveMagmaSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInvolutiveMagmaSigTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClInvolutiveMagmaSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClInvolutiveMagmaSigTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl popcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl popcl x1 ) )
  
  inductionCl _ p psing pprimcl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pprimcl popcl x1 ) (inductionCl _ p psing pprimcl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveMagmaSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInvolutiveMagmaSigTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpInvolutiveMagmaSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpInvolutiveMagmaSigTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol popol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol popol x1 ) )
  
  inductionOp _ p pv pprimol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pprimol popol x1 ) (inductionOp _ p pv pprimol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveMagmaSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInvolutiveMagmaSigTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpInvolutiveMagmaSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpInvolutiveMagmaSigTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x2 ) )
  
  primL' : (  (InvolutiveMagmaSigTerm   → InvolutiveMagmaSigTerm  ))
  primL' x1  = (primL x1 )
  
  opL' : (  (InvolutiveMagmaSigTerm   → (InvolutiveMagmaSigTerm   → InvolutiveMagmaSigTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (InvolutiveMagmaSigTerm  → (Staged InvolutiveMagmaSigTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveMagmaSigTerm A )  → (ClInvolutiveMagmaSigTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  opCl' : ({A  : Set }  → ((ClInvolutiveMagmaSigTerm A )  → ((ClInvolutiveMagmaSigTerm A )  → (ClInvolutiveMagmaSigTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveMagmaSigTerm A ) → (Staged (ClInvolutiveMagmaSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveMagmaSigTerm n )  → (OpInvolutiveMagmaSigTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  opOL' : ({n  : Nat}  → ((OpInvolutiveMagmaSigTerm n )  → ((OpInvolutiveMagmaSigTerm n )  → (OpInvolutiveMagmaSigTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveMagmaSigTerm n ) → (Staged (OpInvolutiveMagmaSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveMagmaSigTerm2 n A )  → (OpInvolutiveMagmaSigTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveMagmaSigTerm2 n A )  → ((OpInvolutiveMagmaSigTerm2 n A )  → (OpInvolutiveMagmaSigTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveMagmaSigTerm2 n A ) → (Staged (OpInvolutiveMagmaSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))