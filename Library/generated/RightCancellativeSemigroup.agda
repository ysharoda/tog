
 module RightCancellativeSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightCancellativeSemigroup (A  : Set )  : Set where
    constructor RightCancellativeSemigroupC
    field
      op : (A  → (A  → A ))
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      rightCancellative : ({x y z  : A }  → ((op x z ) ≡ (op y z ) → x  ≡ y )) 
  
  open RightCancellativeSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      rightCancellativeP : ({xP yP zP  : (Prod AP AP )}  → ((opP xP zP ) ≡ (opP yP zP ) → xP  ≡ yP )) 
  
  record Hom (A1 A2  : Set ) (Ri1  : (RightCancellativeSemigroup A1 )) (Ri2  : (RightCancellativeSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightCancellativeSemigroup A1 )) (Ri2  : (RightCancellativeSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) )))) 
  
  data RightCancellativeSemigroupTerm  : Set where
    opL : (RightCancellativeSemigroupTerm   → (RightCancellativeSemigroupTerm   → RightCancellativeSemigroupTerm  )) 
  
  data ClRightCancellativeSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClRightCancellativeSemigroupTerm A ) )
    opCl : ((ClRightCancellativeSemigroupTerm A )  → ((ClRightCancellativeSemigroupTerm A )  → (ClRightCancellativeSemigroupTerm A ) )) 
  
  data OpRightCancellativeSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightCancellativeSemigroupTerm n ) )
    opOL : ((OpRightCancellativeSemigroupTerm n )  → ((OpRightCancellativeSemigroupTerm n )  → (OpRightCancellativeSemigroupTerm n ) )) 
  
  data OpRightCancellativeSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightCancellativeSemigroupTerm2 n A ) )
    sing2 : (A  → (OpRightCancellativeSemigroupTerm2 n A ) )
    opOL2 : ((OpRightCancellativeSemigroupTerm2 n A )  → ((OpRightCancellativeSemigroupTerm2 n A )  → (OpRightCancellativeSemigroupTerm2 n A ) )) 
  
  simplifyB : (RightCancellativeSemigroupTerm  → RightCancellativeSemigroupTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRightCancellativeSemigroupTerm A ) → (ClRightCancellativeSemigroupTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRightCancellativeSemigroupTerm n ) → (OpRightCancellativeSemigroupTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRightCancellativeSemigroupTerm2 n A ) → (OpRightCancellativeSemigroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((RightCancellativeSemigroup A ) → (RightCancellativeSemigroupTerm  → A )))
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightCancellativeSemigroup A ) → ((ClRightCancellativeSemigroupTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightCancellativeSemigroup A ) → ((Vec A n ) → ((OpRightCancellativeSemigroupTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightCancellativeSemigroup A ) → ((Vec A n ) → ((OpRightCancellativeSemigroupTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightCancellativeSemigroupTerm  → Set ))  → (((x1 x2  : RightCancellativeSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : RightCancellativeSemigroupTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightCancellativeSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRightCancellativeSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClRightCancellativeSemigroupTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightCancellativeSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRightCancellativeSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpRightCancellativeSemigroupTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightCancellativeSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRightCancellativeSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpRightCancellativeSemigroupTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (RightCancellativeSemigroupTerm   → (RightCancellativeSemigroupTerm   → RightCancellativeSemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (RightCancellativeSemigroupTerm  → (Staged RightCancellativeSemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClRightCancellativeSemigroupTerm A )  → ((ClRightCancellativeSemigroupTerm A )  → (ClRightCancellativeSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightCancellativeSemigroupTerm A ) → (Staged (ClRightCancellativeSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpRightCancellativeSemigroupTerm n )  → ((OpRightCancellativeSemigroupTerm n )  → (OpRightCancellativeSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightCancellativeSemigroupTerm n ) → (Staged (OpRightCancellativeSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightCancellativeSemigroupTerm2 n A )  → ((OpRightCancellativeSemigroupTerm2 n A )  → (OpRightCancellativeSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightCancellativeSemigroupTerm2 n A ) → (Staged (OpRightCancellativeSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
