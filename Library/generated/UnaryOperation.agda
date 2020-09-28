module UnaryOperation  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record UnaryOperation (A  : Set )  : Set where
    constructor UnaryOperationC
    field
      prim : (A  → A )
  open UnaryOperation
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
  record Hom (A1 A2  : Set ) (Un1  : (UnaryOperation A1 )) (Un2  : (UnaryOperation A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Un1 ) x1 ) ) ≡ ((prim Un2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (Un1  : (UnaryOperation A1 )) (Un2  : (UnaryOperation A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Un1 ) x1 ) ((prim Un2 ) y1 ) )))
  data UnaryOperationTerm  : Set where
    primL : (UnaryOperationTerm   → UnaryOperationTerm  )
  data ClUnaryOperationTerm (A  : Set )  : Set where
    sing : (A  → (ClUnaryOperationTerm A ) )
    primCl : ((ClUnaryOperationTerm A )  → (ClUnaryOperationTerm A ) )
  data OpUnaryOperationTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpUnaryOperationTerm n ) )
    primOL : ((OpUnaryOperationTerm n )  → (OpUnaryOperationTerm n ) )
  data OpUnaryOperationTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpUnaryOperationTerm2 n A ) )
    sing2 : (A  → (OpUnaryOperationTerm2 n A ) )
    primOL2 : ((OpUnaryOperationTerm2 n A )  → (OpUnaryOperationTerm2 n A ) )
  evalB : ({A  : Set }  → ((UnaryOperation A ) → (UnaryOperationTerm  → A )))
  evalB Un (primL x1 )  = ((prim Un ) (evalB Un x1 ) )
  
  evalCl : ({A  : Set }  → ((UnaryOperation A ) → ((ClUnaryOperationTerm A ) → A )))
  evalCl Un (sing x1 )  = x1 
  
  evalCl Un (primCl x1 )  = ((prim Un ) (evalCl Un x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((UnaryOperation A ) → ((Vec A n ) → ((OpUnaryOperationTerm n ) → A ))))
  evalOp n Un vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Un vars (primOL x1 )  = ((prim Un ) (evalOp n Un vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((UnaryOperation A ) → ((Vec A n ) → ((OpUnaryOperationTerm2 n A ) → A ))))
  evalOpE n Un vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Un vars (sing2 x1 )  = x1 
  
  evalOpE n Un vars (primOL2 x1 )  = ((prim Un ) (evalOpE n Un vars x1 ) )
  
  inductionB : ((P  : (UnaryOperationTerm  → Set ))  → (((x1  : UnaryOperationTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : UnaryOperationTerm )  → (P x ))))
  inductionB p ppriml (primL x1 )  = (ppriml _ (inductionB p ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClUnaryOperationTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClUnaryOperationTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClUnaryOperationTerm A ))  → (P x )))))
  inductionCl _ p psing pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpUnaryOperationTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpUnaryOperationTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpUnaryOperationTerm n ))  → (P x )))))
  inductionOp _ p pv pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpUnaryOperationTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpUnaryOperationTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpUnaryOperationTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 x1 ) )
  
  primL' : (  (UnaryOperationTerm   → UnaryOperationTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (UnaryOperationTerm  → (Staged UnaryOperationTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  primCl' : ({A  : Set }  → ((ClUnaryOperationTerm A )  → (ClUnaryOperationTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClUnaryOperationTerm A ) → (Staged (ClUnaryOperationTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  primOL' : ({n  : Nat}  → ((OpUnaryOperationTerm n )  → (OpUnaryOperationTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpUnaryOperationTerm n ) → (Staged (OpUnaryOperationTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpUnaryOperationTerm2 n A )  → (OpUnaryOperationTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpUnaryOperationTerm2 n A ) → (Staged (OpUnaryOperationTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )