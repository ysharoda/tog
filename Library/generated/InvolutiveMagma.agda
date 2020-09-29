
 module InvolutiveMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveMagma (A  : Set )  : Set where
    constructor InvolutiveMagmaC
    field
      prim : (A  → A )
      involutive_prim : ({x  : A }  → (prim (prim x ) ) ≡ x )
      op : (A  → (A  → A ))
      antidis_prim_op : ({x y  : A }  → (prim (op x y ) ) ≡ (op (prim y ) (prim x ) )) 
  
  open InvolutiveMagma
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
      involutive_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ xP )
      antidis_prim_opP : ({xP yP  : (Prod AP AP )}  → (primP (opP xP yP ) ) ≡ (opP (primP yP ) (primP xP ) )) 
  
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveMagma A1 )) (In2  : (InvolutiveMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveMagma A1 )) (In2  : (InvolutiveMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) )))) 
  
  data InvolutiveMagmaTerm  : Set where
    primL : (InvolutiveMagmaTerm   → InvolutiveMagmaTerm  )
    opL : (InvolutiveMagmaTerm   → (InvolutiveMagmaTerm   → InvolutiveMagmaTerm  )) 
  
  data ClInvolutiveMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveMagmaTerm A ) )
    primCl : ((ClInvolutiveMagmaTerm A )  → (ClInvolutiveMagmaTerm A ) )
    opCl : ((ClInvolutiveMagmaTerm A )  → ((ClInvolutiveMagmaTerm A )  → (ClInvolutiveMagmaTerm A ) )) 
  
  data OpInvolutiveMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveMagmaTerm n ) )
    primOL : ((OpInvolutiveMagmaTerm n )  → (OpInvolutiveMagmaTerm n ) )
    opOL : ((OpInvolutiveMagmaTerm n )  → ((OpInvolutiveMagmaTerm n )  → (OpInvolutiveMagmaTerm n ) )) 
  
  data OpInvolutiveMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveMagmaTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveMagmaTerm2 n A ) )
    primOL2 : ((OpInvolutiveMagmaTerm2 n A )  → (OpInvolutiveMagmaTerm2 n A ) )
    opOL2 : ((OpInvolutiveMagmaTerm2 n A )  → ((OpInvolutiveMagmaTerm2 n A )  → (OpInvolutiveMagmaTerm2 n A ) )) 
  
  simplifyB : (InvolutiveMagmaTerm  → InvolutiveMagmaTerm )
  simplifyB (primL (primL x ) )  = x 
  
  simplifyB (opL (primL y ) (primL x ) )  = (primL (opL x y ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInvolutiveMagmaTerm A ) → (ClInvolutiveMagmaTerm A )))
  simplifyCl _ (primCl (primCl x ) )  = x 
  
  simplifyCl _ (opCl (primCl y ) (primCl x ) )  = (primCl (opCl x y ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutiveMagmaTerm n ) → (OpInvolutiveMagmaTerm n )))
  simplifyOp _ (primOL (primOL x ) )  = x 
  
  simplifyOp _ (opOL (primOL y ) (primOL x ) )  = (primOL (opOL x y ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveMagmaTerm2 n A ) → (OpInvolutiveMagmaTerm2 n A )))
  simplifyOpE _ _ (primOL2 (primOL2 x ) )  = x 
  
  simplifyOpE _ _ (opOL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (opOL2 x y ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InvolutiveMagma A ) → (InvolutiveMagmaTerm  → A )))
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveMagma A ) → ((ClInvolutiveMagmaTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveMagma A ) → ((Vec A n ) → ((OpInvolutiveMagmaTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveMagma A ) → ((Vec A n ) → ((OpInvolutiveMagmaTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  inductionB : ((P  : (InvolutiveMagmaTerm  → Set ))  → (((x1  : InvolutiveMagmaTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : InvolutiveMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : InvolutiveMagmaTerm )  → (P x )))))
  inductionB p ppriml popl (primL x1 )  = (ppriml _ (inductionB p ppriml popl x1 ) )
  
  inductionB p ppriml popl (opL x1 x2 )  = (popl _ _ (inductionB p ppriml popl x1 ) (inductionB p ppriml popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInvolutiveMagmaTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClInvolutiveMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClInvolutiveMagmaTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl popcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl popcl x1 ) )
  
  inductionCl _ p psing pprimcl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pprimcl popcl x1 ) (inductionCl _ p psing pprimcl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInvolutiveMagmaTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpInvolutiveMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpInvolutiveMagmaTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol popol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol popol x1 ) )
  
  inductionOp _ p pv pprimol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pprimol popol x1 ) (inductionOp _ p pv pprimol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInvolutiveMagmaTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpInvolutiveMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpInvolutiveMagmaTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x2 ) )
  
  primL' : (  (InvolutiveMagmaTerm   → InvolutiveMagmaTerm  ))
  primL' x1  = (primL x1 )
  
  opL' : (  (InvolutiveMagmaTerm   → (InvolutiveMagmaTerm   → InvolutiveMagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (InvolutiveMagmaTerm  → (Staged InvolutiveMagmaTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveMagmaTerm A )  → (ClInvolutiveMagmaTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  opCl' : ({A  : Set }  → ((ClInvolutiveMagmaTerm A )  → ((ClInvolutiveMagmaTerm A )  → (ClInvolutiveMagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveMagmaTerm A ) → (Staged (ClInvolutiveMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveMagmaTerm n )  → (OpInvolutiveMagmaTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  opOL' : ({n  : Nat}  → ((OpInvolutiveMagmaTerm n )  → ((OpInvolutiveMagmaTerm n )  → (OpInvolutiveMagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveMagmaTerm n ) → (Staged (OpInvolutiveMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveMagmaTerm2 n A )  → (OpInvolutiveMagmaTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveMagmaTerm2 n A )  → ((OpInvolutiveMagmaTerm2 n A )  → (OpInvolutiveMagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveMagmaTerm2 n A ) → (Staged (OpInvolutiveMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
