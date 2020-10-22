
 module CancellativeSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCancellativeSemigroup (A  : Set ) (op  : (A  → (A  → A )))  : Set where
    constructor IsCancellativeSemigroupC
    field
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      leftCancellative : ({x y z  : A }  → ((op z x ) ≡ (op z y ) → x  ≡ y ))
      rightCancellative : ({x y z  : A }  → ((op x z ) ≡ (op y z ) → x  ≡ y )) 
  
  record CancellativeSemigroup (A  : Set )  : Set where
    constructor CancellativeSemigroupC
    field
      op : (A  → (A  → A ))
      isCancellativeSemigroup : (IsCancellativeSemigroup A op ) 
  
  open CancellativeSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      leftCancellativeP : ({xP yP zP  : (Prod AP AP )}  → ((opP zP xP ) ≡ (opP zP yP ) → xP  ≡ yP ))
      rightCancellativeP : ({xP yP zP  : (Prod AP AP )}  → ((opP xP zP ) ≡ (opP yP zP ) → xP  ≡ yP )) 
  
  record Hom (A1 A2  : Set ) (Ca1  : (CancellativeSemigroup A1 )) (Ca2  : (CancellativeSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ca1 ) x1 x2 ) ) ≡ ((op Ca2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ca1  : (CancellativeSemigroup A1 )) (Ca2  : (CancellativeSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ca1 ) x1 x2 ) ((op Ca2 ) y1 y2 ) )))) 
  
  data CancellativeSemigroupTerm  : Set where
    opL : (CancellativeSemigroupTerm   → (CancellativeSemigroupTerm   → CancellativeSemigroupTerm  )) 
  
  data ClCancellativeSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClCancellativeSemigroupTerm A ) )
    opCl : ((ClCancellativeSemigroupTerm A )  → ((ClCancellativeSemigroupTerm A )  → (ClCancellativeSemigroupTerm A ) )) 
  
  data OpCancellativeSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCancellativeSemigroupTerm n ) )
    opOL : ((OpCancellativeSemigroupTerm n )  → ((OpCancellativeSemigroupTerm n )  → (OpCancellativeSemigroupTerm n ) )) 
  
  data OpCancellativeSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCancellativeSemigroupTerm2 n A ) )
    sing2 : (A  → (OpCancellativeSemigroupTerm2 n A ) )
    opOL2 : ((OpCancellativeSemigroupTerm2 n A )  → ((OpCancellativeSemigroupTerm2 n A )  → (OpCancellativeSemigroupTerm2 n A ) )) 
  
  simplifyB : (CancellativeSemigroupTerm  → CancellativeSemigroupTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClCancellativeSemigroupTerm A ) → (ClCancellativeSemigroupTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpCancellativeSemigroupTerm n ) → (OpCancellativeSemigroupTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpCancellativeSemigroupTerm2 n A ) → (OpCancellativeSemigroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((CancellativeSemigroup A ) → (CancellativeSemigroupTerm  → A )))
  evalB Ca (opL x1 x2 )  = ((op Ca ) (evalB Ca x1 ) (evalB Ca x2 ) )
  
  evalCl : ({A  : Set }  → ((CancellativeSemigroup A ) → ((ClCancellativeSemigroupTerm A ) → A )))
  evalCl Ca (sing x1 )  = x1 
  
  evalCl Ca (opCl x1 x2 )  = ((op Ca ) (evalCl Ca x1 ) (evalCl Ca x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CancellativeSemigroup A ) → ((Vec A n ) → ((OpCancellativeSemigroupTerm n ) → A ))))
  evalOp n Ca vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ca vars (opOL x1 x2 )  = ((op Ca ) (evalOp n Ca vars x1 ) (evalOp n Ca vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CancellativeSemigroup A ) → ((Vec A n ) → ((OpCancellativeSemigroupTerm2 n A ) → A ))))
  evalOpE n Ca vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ca vars (sing2 x1 )  = x1 
  
  evalOpE n Ca vars (opOL2 x1 x2 )  = ((op Ca ) (evalOpE n Ca vars x1 ) (evalOpE n Ca vars x2 ) )
  
  inductionB : ((P  : (CancellativeSemigroupTerm  → Set ))  → (((x1 x2  : CancellativeSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : CancellativeSemigroupTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClCancellativeSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCancellativeSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClCancellativeSemigroupTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpCancellativeSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCancellativeSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpCancellativeSemigroupTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCancellativeSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCancellativeSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpCancellativeSemigroupTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (CancellativeSemigroupTerm   → (CancellativeSemigroupTerm   → CancellativeSemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (CancellativeSemigroupTerm  → (Staged CancellativeSemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClCancellativeSemigroupTerm A )  → ((ClCancellativeSemigroupTerm A )  → (ClCancellativeSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClCancellativeSemigroupTerm A ) → (Staged (ClCancellativeSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpCancellativeSemigroupTerm n )  → ((OpCancellativeSemigroupTerm n )  → (OpCancellativeSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpCancellativeSemigroupTerm n ) → (Staged (OpCancellativeSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCancellativeSemigroupTerm2 n A )  → ((OpCancellativeSemigroupTerm2 n A )  → (OpCancellativeSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCancellativeSemigroupTerm2 n A ) → (Staged (OpCancellativeSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
