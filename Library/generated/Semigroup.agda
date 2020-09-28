module Semigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Semigroup (A  : Set )  : Set where
    constructor SemigroupC
    field
      op : (A  → (A  → A ))
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
  open Semigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
  record Hom (A1 A2  : Set ) (Se1  : (Semigroup A1 )) (Se2  : (Semigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Se1 ) x1 x2 ) ) ≡ ((op Se2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Se1  : (Semigroup A1 )) (Se2  : (Semigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Se1 ) x1 x2 ) ((op Se2 ) y1 y2 ) ))))
  data SemigroupTerm  : Set where
    opL : (SemigroupTerm   → (SemigroupTerm   → SemigroupTerm  ))
  data ClSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClSemigroupTerm A ) )
    opCl : ((ClSemigroupTerm A )  → ((ClSemigroupTerm A )  → (ClSemigroupTerm A ) ))
  data OpSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpSemigroupTerm n ) )
    opOL : ((OpSemigroupTerm n )  → ((OpSemigroupTerm n )  → (OpSemigroupTerm n ) ))
  data OpSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpSemigroupTerm2 n A ) )
    sing2 : (A  → (OpSemigroupTerm2 n A ) )
    opOL2 : ((OpSemigroupTerm2 n A )  → ((OpSemigroupTerm2 n A )  → (OpSemigroupTerm2 n A ) ))
  evalB : ({A  : Set }  → ((Semigroup A ) → (SemigroupTerm  → A )))
  evalB Se (opL x1 x2 )  = ((op Se ) (evalB Se x1 ) (evalB Se x2 ) )
  
  evalCl : ({A  : Set }  → ((Semigroup A ) → ((ClSemigroupTerm A ) → A )))
  evalCl Se (sing x1 )  = x1 
  
  evalCl Se (opCl x1 x2 )  = ((op Se ) (evalCl Se x1 ) (evalCl Se x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Semigroup A ) → ((Vec A n ) → ((OpSemigroupTerm n ) → A ))))
  evalOp n Se vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Se vars (opOL x1 x2 )  = ((op Se ) (evalOp n Se vars x1 ) (evalOp n Se vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Semigroup A ) → ((Vec A n ) → ((OpSemigroupTerm2 n A ) → A ))))
  evalOpE n Se vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Se vars (sing2 x1 )  = x1 
  
  evalOpE n Se vars (opOL2 x1 x2 )  = ((op Se ) (evalOpE n Se vars x1 ) (evalOpE n Se vars x2 ) )
  
  inductionB : ((P  : (SemigroupTerm  → Set ))  → (((x1 x2  : SemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : SemigroupTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClSemigroupTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpSemigroupTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpSemigroupTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (SemigroupTerm   → (SemigroupTerm   → SemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (SemigroupTerm  → (Staged SemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClSemigroupTerm A )  → ((ClSemigroupTerm A )  → (ClSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClSemigroupTerm A ) → (Staged (ClSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpSemigroupTerm n )  → ((OpSemigroupTerm n )  → (OpSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpSemigroupTerm n ) → (Staged (OpSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpSemigroupTerm2 n A )  → ((OpSemigroupTerm2 n A )  → (OpSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpSemigroupTerm2 n A ) → (Staged (OpSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))