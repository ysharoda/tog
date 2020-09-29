
 module RectangularBand  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RectangularBand (A  : Set )  : Set where
    constructor RectangularBandC
    field
      op : (A  → (A  → A ))
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      idempotent_op : ({x  : A }  → (op x x ) ≡ x )
      middleCommute_* : ({x y z  : A }  → (op (op (op x y ) z ) x ) ≡ (op (op (op x z ) y ) x )) 
  
  open RectangularBand
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      idempotent_opP : ({xP  : (Prod AP AP )}  → (opP xP xP ) ≡ xP )
      middleCommute_*P : ({xP yP zP  : (Prod AP AP )}  → (opP (opP (opP xP yP ) zP ) xP ) ≡ (opP (opP (opP xP zP ) yP ) xP )) 
  
  record Hom (A1 A2  : Set ) (Re1  : (RectangularBand A1 )) (Re2  : (RectangularBand A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Re1 ) x1 x2 ) ) ≡ ((op Re2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Re1  : (RectangularBand A1 )) (Re2  : (RectangularBand A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Re1 ) x1 x2 ) ((op Re2 ) y1 y2 ) )))) 
  
  data RectangularBandTerm  : Set where
    opL : (RectangularBandTerm   → (RectangularBandTerm   → RectangularBandTerm  )) 
  
  data ClRectangularBandTerm (A  : Set )  : Set where
    sing : (A  → (ClRectangularBandTerm A ) )
    opCl : ((ClRectangularBandTerm A )  → ((ClRectangularBandTerm A )  → (ClRectangularBandTerm A ) )) 
  
  data OpRectangularBandTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRectangularBandTerm n ) )
    opOL : ((OpRectangularBandTerm n )  → ((OpRectangularBandTerm n )  → (OpRectangularBandTerm n ) )) 
  
  data OpRectangularBandTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRectangularBandTerm2 n A ) )
    sing2 : (A  → (OpRectangularBandTerm2 n A ) )
    opOL2 : ((OpRectangularBandTerm2 n A )  → ((OpRectangularBandTerm2 n A )  → (OpRectangularBandTerm2 n A ) )) 
  
  simplifyB : (RectangularBandTerm  → RectangularBandTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRectangularBandTerm A ) → (ClRectangularBandTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRectangularBandTerm n ) → (OpRectangularBandTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRectangularBandTerm2 n A ) → (OpRectangularBandTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((RectangularBand A ) → (RectangularBandTerm  → A )))
  evalB Re (opL x1 x2 )  = ((op Re ) (evalB Re x1 ) (evalB Re x2 ) )
  
  evalCl : ({A  : Set }  → ((RectangularBand A ) → ((ClRectangularBandTerm A ) → A )))
  evalCl Re (sing x1 )  = x1 
  
  evalCl Re (opCl x1 x2 )  = ((op Re ) (evalCl Re x1 ) (evalCl Re x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RectangularBand A ) → ((Vec A n ) → ((OpRectangularBandTerm n ) → A ))))
  evalOp n Re vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Re vars (opOL x1 x2 )  = ((op Re ) (evalOp n Re vars x1 ) (evalOp n Re vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RectangularBand A ) → ((Vec A n ) → ((OpRectangularBandTerm2 n A ) → A ))))
  evalOpE n Re vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Re vars (sing2 x1 )  = x1 
  
  evalOpE n Re vars (opOL2 x1 x2 )  = ((op Re ) (evalOpE n Re vars x1 ) (evalOpE n Re vars x2 ) )
  
  inductionB : ((P  : (RectangularBandTerm  → Set ))  → (((x1 x2  : RectangularBandTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : RectangularBandTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRectangularBandTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRectangularBandTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClRectangularBandTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRectangularBandTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRectangularBandTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpRectangularBandTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRectangularBandTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRectangularBandTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpRectangularBandTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (RectangularBandTerm   → (RectangularBandTerm   → RectangularBandTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (RectangularBandTerm  → (Staged RectangularBandTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClRectangularBandTerm A )  → ((ClRectangularBandTerm A )  → (ClRectangularBandTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRectangularBandTerm A ) → (Staged (ClRectangularBandTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpRectangularBandTerm n )  → ((OpRectangularBandTerm n )  → (OpRectangularBandTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRectangularBandTerm n ) → (Staged (OpRectangularBandTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRectangularBandTerm2 n A )  → ((OpRectangularBandTerm2 n A )  → (OpRectangularBandTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRectangularBandTerm2 n A ) → (Staged (OpRectangularBandTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
