module InvolutivePointedSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutivePointedSemigroup (A  : Set )  : Set where
    constructor InvolutivePointedSemigroupC
    field
      op : (A  → (A  → A ))
      e : A 
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      prim : (A  → A )
      involutive_prim : ({x  : A }  → (prim (prim x ) ) ≡ x )
      antidis_prim_op : ({x y  : A }  → (prim (op x y ) ) ≡ (op (prim y ) (prim x ) ))
  open InvolutivePointedSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS 
      primS : (AS  → AS )
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      primP : ((Prod AP AP ) → (Prod AP AP ))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      involutive_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ xP )
      antidis_prim_opP : ({xP yP  : (Prod AP AP )}  → (primP (opP xP yP ) ) ≡ (opP (primP yP ) (primP xP ) ))
  record Hom (A1 A2  : Set ) (In1  : (InvolutivePointedSemigroup A1 )) (In2  : (InvolutivePointedSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e In1 )  ) ≡ (e In2 ) )
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutivePointedSemigroup A1 )) (In2  : (InvolutivePointedSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) ))))
      interp-e : (  (interp (e In1 )  (e In2 )  ))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
  data InvolutivePointedSemigroupTerm  : Set where
    opL : (InvolutivePointedSemigroupTerm   → (InvolutivePointedSemigroupTerm   → InvolutivePointedSemigroupTerm  ))
    eL : InvolutivePointedSemigroupTerm  
    primL : (InvolutivePointedSemigroupTerm   → InvolutivePointedSemigroupTerm  )
  data ClInvolutivePointedSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutivePointedSemigroupTerm A ) )
    opCl : ((ClInvolutivePointedSemigroupTerm A )  → ((ClInvolutivePointedSemigroupTerm A )  → (ClInvolutivePointedSemigroupTerm A ) ))
    eCl : (ClInvolutivePointedSemigroupTerm A ) 
    primCl : ((ClInvolutivePointedSemigroupTerm A )  → (ClInvolutivePointedSemigroupTerm A ) )
  data OpInvolutivePointedSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutivePointedSemigroupTerm n ) )
    opOL : ((OpInvolutivePointedSemigroupTerm n )  → ((OpInvolutivePointedSemigroupTerm n )  → (OpInvolutivePointedSemigroupTerm n ) ))
    eOL : (OpInvolutivePointedSemigroupTerm n ) 
    primOL : ((OpInvolutivePointedSemigroupTerm n )  → (OpInvolutivePointedSemigroupTerm n ) )
  data OpInvolutivePointedSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutivePointedSemigroupTerm2 n A ) )
    sing2 : (A  → (OpInvolutivePointedSemigroupTerm2 n A ) )
    opOL2 : ((OpInvolutivePointedSemigroupTerm2 n A )  → ((OpInvolutivePointedSemigroupTerm2 n A )  → (OpInvolutivePointedSemigroupTerm2 n A ) ))
    eOL2 : (OpInvolutivePointedSemigroupTerm2 n A ) 
    primOL2 : ((OpInvolutivePointedSemigroupTerm2 n A )  → (OpInvolutivePointedSemigroupTerm2 n A ) )
  evalB : ({A  : Set }  → ((InvolutivePointedSemigroup A ) → (InvolutivePointedSemigroupTerm  → A )))
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In eL  = (e In ) 
  
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((InvolutivePointedSemigroup A ) → ((ClInvolutivePointedSemigroupTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In eCl  = (e In ) 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutivePointedSemigroup A ) → ((Vec A n ) → ((OpInvolutivePointedSemigroupTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars eOL  = (e In ) 
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutivePointedSemigroup A ) → ((Vec A n ) → ((OpInvolutivePointedSemigroupTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars eOL2  = (e In ) 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InvolutivePointedSemigroupTerm  → Set ))  → (((x1 x2  : InvolutivePointedSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → (((x1  : InvolutivePointedSemigroupTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : InvolutivePointedSemigroupTerm )  → (P x ))))))
  inductionB p popl pel ppriml (opL x1 x2 )  = (popl _ _ (inductionB p popl pel ppriml x1 ) (inductionB p popl pel ppriml x2 ) )
  
  inductionB p popl pel ppriml eL  = pel 
  
  inductionB p popl pel ppriml (primL x1 )  = (ppriml _ (inductionB p popl pel ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutivePointedSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClInvolutivePointedSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → (((x1  : (ClInvolutivePointedSemigroupTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClInvolutivePointedSemigroupTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl pecl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl pprimcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl pprimcl x1 ) (inductionCl _ p psing popcl pecl pprimcl x2 ) )
  
  inductionCl _ p psing popcl pecl pprimcl eCl  = pecl 
  
  inductionCl _ p psing popcl pecl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing popcl pecl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutivePointedSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpInvolutivePointedSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → (((x1  : (OpInvolutivePointedSemigroupTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpInvolutivePointedSemigroupTerm n ))  → (P x )))))))
  inductionOp _ p pv popol peol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol pprimol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol pprimol x1 ) (inductionOp _ p pv popol peol pprimol x2 ) )
  
  inductionOp _ p pv popol peol pprimol eOL  = peol 
  
  inductionOp _ p pv popol peol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv popol peol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutivePointedSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpInvolutivePointedSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → (((x1  : (OpInvolutivePointedSemigroupTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpInvolutivePointedSemigroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 pprimol2 x1 ) )
  
  opL' : (  (InvolutivePointedSemigroupTerm   → (InvolutivePointedSemigroupTerm   → InvolutivePointedSemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  InvolutivePointedSemigroupTerm  )
  eL'  = eL 
  
  primL' : (  (InvolutivePointedSemigroupTerm   → InvolutivePointedSemigroupTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (InvolutivePointedSemigroupTerm  → (Staged InvolutivePointedSemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  opCl' : ({A  : Set }  → ((ClInvolutivePointedSemigroupTerm A )  → ((ClInvolutivePointedSemigroupTerm A )  → (ClInvolutivePointedSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClInvolutivePointedSemigroupTerm A ) )
  eCl'  = eCl 
  
  primCl' : ({A  : Set }  → ((ClInvolutivePointedSemigroupTerm A )  → (ClInvolutivePointedSemigroupTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInvolutivePointedSemigroupTerm A ) → (Staged (ClInvolutivePointedSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  opOL' : ({n  : Nat}  → ((OpInvolutivePointedSemigroupTerm n )  → ((OpInvolutivePointedSemigroupTerm n )  → (OpInvolutivePointedSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpInvolutivePointedSemigroupTerm n ) )
  eOL'  = eOL 
  
  primOL' : ({n  : Nat}  → ((OpInvolutivePointedSemigroupTerm n )  → (OpInvolutivePointedSemigroupTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutivePointedSemigroupTerm n ) → (Staged (OpInvolutivePointedSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutivePointedSemigroupTerm2 n A )  → ((OpInvolutivePointedSemigroupTerm2 n A )  → (OpInvolutivePointedSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpInvolutivePointedSemigroupTerm2 n A ) )
  eOL2'  = eOL2 
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutivePointedSemigroupTerm2 n A )  → (OpInvolutivePointedSemigroupTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutivePointedSemigroupTerm2 n A ) → (Staged (OpInvolutivePointedSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 
      primT : ((Repr A )  → (Repr A ) )