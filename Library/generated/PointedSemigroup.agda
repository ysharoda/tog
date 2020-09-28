module PointedSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedSemigroup (A  : Set )  : Set where
    constructor PointedSemigroupC
    field
      op : (A  → (A  → A ))
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      e : A 
  open PointedSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
  record Hom (A1 A2  : Set ) (Po1  : (PointedSemigroup A1 )) (Po2  : (PointedSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Po1 ) x1 x2 ) ) ≡ ((op Po2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Po1 )  ) ≡ (e Po2 ) )
  record RelInterp (A1 A2  : Set ) (Po1  : (PointedSemigroup A1 )) (Po2  : (PointedSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Po1 ) x1 x2 ) ((op Po2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Po1 )  (e Po2 )  ))
  data PointedSemigroupTerm  : Set where
    opL : (PointedSemigroupTerm   → (PointedSemigroupTerm   → PointedSemigroupTerm  ))
    eL : PointedSemigroupTerm  
  data ClPointedSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClPointedSemigroupTerm A ) )
    opCl : ((ClPointedSemigroupTerm A )  → ((ClPointedSemigroupTerm A )  → (ClPointedSemigroupTerm A ) ))
    eCl : (ClPointedSemigroupTerm A ) 
  data OpPointedSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointedSemigroupTerm n ) )
    opOL : ((OpPointedSemigroupTerm n )  → ((OpPointedSemigroupTerm n )  → (OpPointedSemigroupTerm n ) ))
    eOL : (OpPointedSemigroupTerm n ) 
  data OpPointedSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointedSemigroupTerm2 n A ) )
    sing2 : (A  → (OpPointedSemigroupTerm2 n A ) )
    opOL2 : ((OpPointedSemigroupTerm2 n A )  → ((OpPointedSemigroupTerm2 n A )  → (OpPointedSemigroupTerm2 n A ) ))
    eOL2 : (OpPointedSemigroupTerm2 n A ) 
  evalB : ({A  : Set }  → ((PointedSemigroup A ) → (PointedSemigroupTerm  → A )))
  evalB Po (opL x1 x2 )  = ((op Po ) (evalB Po x1 ) (evalB Po x2 ) )
  
  evalB Po eL  = (e Po ) 
  
  evalCl : ({A  : Set }  → ((PointedSemigroup A ) → ((ClPointedSemigroupTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po (opCl x1 x2 )  = ((op Po ) (evalCl Po x1 ) (evalCl Po x2 ) )
  
  evalCl Po eCl  = (e Po ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PointedSemigroup A ) → ((Vec A n ) → ((OpPointedSemigroupTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars (opOL x1 x2 )  = ((op Po ) (evalOp n Po vars x1 ) (evalOp n Po vars x2 ) )
  
  evalOp n Po vars eOL  = (e Po ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PointedSemigroup A ) → ((Vec A n ) → ((OpPointedSemigroupTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars (opOL2 x1 x2 )  = ((op Po ) (evalOpE n Po vars x1 ) (evalOpE n Po vars x2 ) )
  
  evalOpE n Po vars eOL2  = (e Po ) 
  
  inductionB : ((P  : (PointedSemigroupTerm  → Set ))  → (((x1 x2  : PointedSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : PointedSemigroupTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClPointedSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClPointedSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClPointedSemigroupTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpPointedSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpPointedSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpPointedSemigroupTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointedSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpPointedSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpPointedSemigroupTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (PointedSemigroupTerm   → (PointedSemigroupTerm   → PointedSemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  PointedSemigroupTerm  )
  eL'  = eL 
  
  stageB : (PointedSemigroupTerm  → (Staged PointedSemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClPointedSemigroupTerm A )  → ((ClPointedSemigroupTerm A )  → (ClPointedSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClPointedSemigroupTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClPointedSemigroupTerm A ) → (Staged (ClPointedSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpPointedSemigroupTerm n )  → ((OpPointedSemigroupTerm n )  → (OpPointedSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpPointedSemigroupTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpPointedSemigroupTerm n ) → (Staged (OpPointedSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpPointedSemigroupTerm2 n A )  → ((OpPointedSemigroupTerm2 n A )  → (OpPointedSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpPointedSemigroupTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedSemigroupTerm2 n A ) → (Staged (OpPointedSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 