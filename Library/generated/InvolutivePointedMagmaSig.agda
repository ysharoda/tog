module InvolutivePointedMagmaSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutivePointedMagmaSig (A  : Set )  : Set where
    constructor InvolutivePointedMagmaSigC
    field
      prim : (A  → A )
      e : A 
      op : (A  → (A  → A ))
  open InvolutivePointedMagmaSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      eS : AS 
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      eP : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
  record Hom (A1 A2  : Set ) (In1  : (InvolutivePointedMagmaSig A1 )) (In2  : (InvolutivePointedMagmaSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
      pres-e : (  (hom (e In1 )  ) ≡ (e In2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutivePointedMagmaSig A1 )) (In2  : (InvolutivePointedMagmaSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
      interp-e : (  (interp (e In1 )  (e In2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) ))))
  data InvolutivePointedMagmaSigTerm  : Set where
    primL : (InvolutivePointedMagmaSigTerm   → InvolutivePointedMagmaSigTerm  )
    eL : InvolutivePointedMagmaSigTerm  
    opL : (InvolutivePointedMagmaSigTerm   → (InvolutivePointedMagmaSigTerm   → InvolutivePointedMagmaSigTerm  ))
  data ClInvolutivePointedMagmaSigTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutivePointedMagmaSigTerm A ) )
    primCl : ((ClInvolutivePointedMagmaSigTerm A )  → (ClInvolutivePointedMagmaSigTerm A ) )
    eCl : (ClInvolutivePointedMagmaSigTerm A ) 
    opCl : ((ClInvolutivePointedMagmaSigTerm A )  → ((ClInvolutivePointedMagmaSigTerm A )  → (ClInvolutivePointedMagmaSigTerm A ) ))
  data OpInvolutivePointedMagmaSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutivePointedMagmaSigTerm n ) )
    primOL : ((OpInvolutivePointedMagmaSigTerm n )  → (OpInvolutivePointedMagmaSigTerm n ) )
    eOL : (OpInvolutivePointedMagmaSigTerm n ) 
    opOL : ((OpInvolutivePointedMagmaSigTerm n )  → ((OpInvolutivePointedMagmaSigTerm n )  → (OpInvolutivePointedMagmaSigTerm n ) ))
  data OpInvolutivePointedMagmaSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutivePointedMagmaSigTerm2 n A ) )
    sing2 : (A  → (OpInvolutivePointedMagmaSigTerm2 n A ) )
    primOL2 : ((OpInvolutivePointedMagmaSigTerm2 n A )  → (OpInvolutivePointedMagmaSigTerm2 n A ) )
    eOL2 : (OpInvolutivePointedMagmaSigTerm2 n A ) 
    opOL2 : ((OpInvolutivePointedMagmaSigTerm2 n A )  → ((OpInvolutivePointedMagmaSigTerm2 n A )  → (OpInvolutivePointedMagmaSigTerm2 n A ) ))
  evalB : ({A  : Set }  → ((InvolutivePointedMagmaSig A ) → (InvolutivePointedMagmaSigTerm  → A )))
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalB In eL  = (e In ) 
  
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalCl : ({A  : Set }  → ((InvolutivePointedMagmaSig A ) → ((ClInvolutivePointedMagmaSigTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalCl In eCl  = (e In ) 
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutivePointedMagmaSig A ) → ((Vec A n ) → ((OpInvolutivePointedMagmaSigTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars eOL  = (e In ) 
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutivePointedMagmaSig A ) → ((Vec A n ) → ((OpInvolutivePointedMagmaSigTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars eOL2  = (e In ) 
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  inductionB : ((P  : (InvolutivePointedMagmaSigTerm  → Set ))  → (((x1  : InvolutivePointedMagmaSigTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((P eL ) → (((x1 x2  : InvolutivePointedMagmaSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : InvolutivePointedMagmaSigTerm )  → (P x ))))))
  inductionB p ppriml pel popl (primL x1 )  = (ppriml _ (inductionB p ppriml pel popl x1 ) )
  
  inductionB p ppriml pel popl eL  = pel 
  
  inductionB p ppriml pel popl (opL x1 x2 )  = (popl _ _ (inductionB p ppriml pel popl x1 ) (inductionB p ppriml pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutivePointedMagmaSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInvolutivePointedMagmaSigTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((P eCl ) → (((x1 x2  : (ClInvolutivePointedMagmaSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClInvolutivePointedMagmaSigTerm A ))  → (P x )))))))
  inductionCl _ p psing pprimcl pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl pecl popcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl pecl popcl x1 ) )
  
  inductionCl _ p psing pprimcl pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pprimcl pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pprimcl pecl popcl x1 ) (inductionCl _ p psing pprimcl pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutivePointedMagmaSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInvolutivePointedMagmaSigTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((P eOL ) → (((x1 x2  : (OpInvolutivePointedMagmaSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpInvolutivePointedMagmaSigTerm n ))  → (P x )))))))
  inductionOp _ p pv pprimol peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol peol popol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol peol popol x1 ) )
  
  inductionOp _ p pv pprimol peol popol eOL  = peol 
  
  inductionOp _ p pv pprimol peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pprimol peol popol x1 ) (inductionOp _ p pv pprimol peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutivePointedMagmaSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInvolutivePointedMagmaSigTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((P eOL2 ) → (((x1 x2  : (OpInvolutivePointedMagmaSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpInvolutivePointedMagmaSigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 peol2 popol2 x2 ) )
  
  primL' : (  (InvolutivePointedMagmaSigTerm   → InvolutivePointedMagmaSigTerm  ))
  primL' x1  = (primL x1 )
  
  eL' : (  InvolutivePointedMagmaSigTerm  )
  eL'  = eL 
  
  opL' : (  (InvolutivePointedMagmaSigTerm   → (InvolutivePointedMagmaSigTerm   → InvolutivePointedMagmaSigTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (InvolutivePointedMagmaSigTerm  → (Staged InvolutivePointedMagmaSigTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClInvolutivePointedMagmaSigTerm A )  → (ClInvolutivePointedMagmaSigTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  eCl' : ({A  : Set }  → (ClInvolutivePointedMagmaSigTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClInvolutivePointedMagmaSigTerm A )  → ((ClInvolutivePointedMagmaSigTerm A )  → (ClInvolutivePointedMagmaSigTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClInvolutivePointedMagmaSigTerm A ) → (Staged (ClInvolutivePointedMagmaSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpInvolutivePointedMagmaSigTerm n )  → (OpInvolutivePointedMagmaSigTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  eOL' : ({n  : Nat}  → (OpInvolutivePointedMagmaSigTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpInvolutivePointedMagmaSigTerm n )  → ((OpInvolutivePointedMagmaSigTerm n )  → (OpInvolutivePointedMagmaSigTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutivePointedMagmaSigTerm n ) → (Staged (OpInvolutivePointedMagmaSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutivePointedMagmaSigTerm2 n A )  → (OpInvolutivePointedMagmaSigTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpInvolutivePointedMagmaSigTerm2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutivePointedMagmaSigTerm2 n A )  → ((OpInvolutivePointedMagmaSigTerm2 n A )  → (OpInvolutivePointedMagmaSigTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutivePointedMagmaSigTerm2 n A ) → (Staged (OpInvolutivePointedMagmaSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))