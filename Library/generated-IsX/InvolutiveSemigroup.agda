
 module InvolutiveSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveSemigroup (A  : Set ) (op  : (A  → (A  → A ))) (prim  : (A  → A ))  : Set where
    constructor IsInvolutiveSemigroupC
    field
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      involutive_prim : ({x  : A }  → (prim (prim x ) ) ≡ x )
      antidis_prim_op : ({x y  : A }  → (prim (op x y ) ) ≡ (op (prim y ) (prim x ) )) 
  
  record InvolutiveSemigroup (A  : Set )  : Set where
    constructor InvolutiveSemigroupC
    field
      op : (A  → (A  → A ))
      prim : (A  → A )
      isInvolutiveSemigroup : (IsInvolutiveSemigroup A op prim ) 
  
  open InvolutiveSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      primS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      primP : ((Prod AP AP ) → (Prod AP AP ))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      involutive_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ xP )
      antidis_prim_opP : ({xP yP  : (Prod AP AP )}  → (primP (opP xP yP ) ) ≡ (opP (primP yP ) (primP xP ) )) 
  
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveSemigroup A1 )) (In2  : (InvolutiveSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveSemigroup A1 )) (In2  : (InvolutiveSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) ))) 
  
  data InvolutiveSemigroupTerm  : Set where
    opL : (InvolutiveSemigroupTerm   → (InvolutiveSemigroupTerm   → InvolutiveSemigroupTerm  ))
    primL : (InvolutiveSemigroupTerm   → InvolutiveSemigroupTerm  ) 
  
  data ClInvolutiveSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveSemigroupTerm A ) )
    opCl : ((ClInvolutiveSemigroupTerm A )  → ((ClInvolutiveSemigroupTerm A )  → (ClInvolutiveSemigroupTerm A ) ))
    primCl : ((ClInvolutiveSemigroupTerm A )  → (ClInvolutiveSemigroupTerm A ) ) 
  
  data OpInvolutiveSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveSemigroupTerm n ) )
    opOL : ((OpInvolutiveSemigroupTerm n )  → ((OpInvolutiveSemigroupTerm n )  → (OpInvolutiveSemigroupTerm n ) ))
    primOL : ((OpInvolutiveSemigroupTerm n )  → (OpInvolutiveSemigroupTerm n ) ) 
  
  data OpInvolutiveSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveSemigroupTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveSemigroupTerm2 n A ) )
    opOL2 : ((OpInvolutiveSemigroupTerm2 n A )  → ((OpInvolutiveSemigroupTerm2 n A )  → (OpInvolutiveSemigroupTerm2 n A ) ))
    primOL2 : ((OpInvolutiveSemigroupTerm2 n A )  → (OpInvolutiveSemigroupTerm2 n A ) ) 
  
  simplifyB : (InvolutiveSemigroupTerm  → InvolutiveSemigroupTerm )
  simplifyB (primL (primL x ) )  = x 
  
  simplifyB (opL (primL y ) (primL x ) )  = (primL (opL x y ) )
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInvolutiveSemigroupTerm A ) → (ClInvolutiveSemigroupTerm A )))
  simplifyCl _ (primCl (primCl x ) )  = x 
  
  simplifyCl _ (opCl (primCl y ) (primCl x ) )  = (primCl (opCl x y ) )
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutiveSemigroupTerm n ) → (OpInvolutiveSemigroupTerm n )))
  simplifyOp _ (primOL (primOL x ) )  = x 
  
  simplifyOp _ (opOL (primOL y ) (primOL x ) )  = (primOL (opOL x y ) )
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveSemigroupTerm2 n A ) → (OpInvolutiveSemigroupTerm2 n A )))
  simplifyOpE _ _ (primOL2 (primOL2 x ) )  = x 
  
  simplifyOpE _ _ (opOL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (opOL2 x y ) )
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InvolutiveSemigroup A ) → (InvolutiveSemigroupTerm  → A )))
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveSemigroup A ) → ((ClInvolutiveSemigroupTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveSemigroup A ) → ((Vec A n ) → ((OpInvolutiveSemigroupTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveSemigroup A ) → ((Vec A n ) → ((OpInvolutiveSemigroupTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InvolutiveSemigroupTerm  → Set ))  → (((x1 x2  : InvolutiveSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1  : InvolutiveSemigroupTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : InvolutiveSemigroupTerm )  → (P x )))))
  inductionB p popl ppriml (opL x1 x2 )  = (popl _ _ (inductionB p popl ppriml x1 ) (inductionB p popl ppriml x2 ) )
  
  inductionB p popl ppriml (primL x1 )  = (ppriml _ (inductionB p popl ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClInvolutiveSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1  : (ClInvolutiveSemigroupTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClInvolutiveSemigroupTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pprimcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pprimcl x1 ) (inductionCl _ p psing popcl pprimcl x2 ) )
  
  inductionCl _ p psing popcl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing popcl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpInvolutiveSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1  : (OpInvolutiveSemigroupTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpInvolutiveSemigroupTerm n ))  → (P x ))))))
  inductionOp _ p pv popol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol pprimol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol pprimol x1 ) (inductionOp _ p pv popol pprimol x2 ) )
  
  inductionOp _ p pv popol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv popol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpInvolutiveSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1  : (OpInvolutiveSemigroupTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpInvolutiveSemigroupTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 pprimol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 popol2 pprimol2 x1 ) )
  
  opL' : (  (InvolutiveSemigroupTerm   → (InvolutiveSemigroupTerm   → InvolutiveSemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  primL' : (  (InvolutiveSemigroupTerm   → InvolutiveSemigroupTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (InvolutiveSemigroupTerm  → (Staged InvolutiveSemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  opCl' : ({A  : Set }  → ((ClInvolutiveSemigroupTerm A )  → ((ClInvolutiveSemigroupTerm A )  → (ClInvolutiveSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveSemigroupTerm A )  → (ClInvolutiveSemigroupTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveSemigroupTerm A ) → (Staged (ClInvolutiveSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  opOL' : ({n  : Nat}  → ((OpInvolutiveSemigroupTerm n )  → ((OpInvolutiveSemigroupTerm n )  → (OpInvolutiveSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveSemigroupTerm n )  → (OpInvolutiveSemigroupTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveSemigroupTerm n ) → (Staged (OpInvolutiveSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveSemigroupTerm2 n A )  → ((OpInvolutiveSemigroupTerm2 n A )  → (OpInvolutiveSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveSemigroupTerm2 n A )  → (OpInvolutiveSemigroupTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveSemigroupTerm2 n A ) → (Staged (OpInvolutiveSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      primT : ((Repr A )  → (Repr A ) ) 
   
