module RightMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightMonoid (A  : Set )  : Set where
    constructor RightMonoidC
    field
      op : (A  → (A  → A ))
      e : A 
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
  open RightMonoid
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
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
  record Hom (A1 A2  : Set ) (Ri1  : (RightMonoid A1 )) (Ri2  : (RightMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Ri1 )  ) ≡ (e Ri2 ) )
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightMonoid A1 )) (Ri2  : (RightMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Ri1 )  (e Ri2 )  ))
  data RightMonoidTerm  : Set where
    opL : (RightMonoidTerm   → (RightMonoidTerm   → RightMonoidTerm  ))
    eL : RightMonoidTerm  
  data ClRightMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClRightMonoidTerm A ) )
    opCl : ((ClRightMonoidTerm A )  → ((ClRightMonoidTerm A )  → (ClRightMonoidTerm A ) ))
    eCl : (ClRightMonoidTerm A ) 
  data OpRightMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightMonoidTerm n ) )
    opOL : ((OpRightMonoidTerm n )  → ((OpRightMonoidTerm n )  → (OpRightMonoidTerm n ) ))
    eOL : (OpRightMonoidTerm n ) 
  data OpRightMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightMonoidTerm2 n A ) )
    sing2 : (A  → (OpRightMonoidTerm2 n A ) )
    opOL2 : ((OpRightMonoidTerm2 n A )  → ((OpRightMonoidTerm2 n A )  → (OpRightMonoidTerm2 n A ) ))
    eOL2 : (OpRightMonoidTerm2 n A ) 
  evalB : ({A  : Set }  → ((RightMonoid A ) → (RightMonoidTerm  → A )))
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri eL  = (e Ri ) 
  
  evalCl : ({A  : Set }  → ((RightMonoid A ) → ((ClRightMonoidTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri eCl  = (e Ri ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightMonoid A ) → ((Vec A n ) → ((OpRightMonoidTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars eOL  = (e Ri ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightMonoid A ) → ((Vec A n ) → ((OpRightMonoidTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars eOL2  = (e Ri ) 
  
  inductionB : ((P  : (RightMonoidTerm  → Set ))  → (((x1 x2  : RightMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : RightMonoidTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClRightMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRightMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClRightMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpRightMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRightMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpRightMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRightMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpRightMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (RightMonoidTerm   → (RightMonoidTerm   → RightMonoidTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  RightMonoidTerm  )
  eL'  = eL 
  
  stageB : (RightMonoidTerm  → (Staged RightMonoidTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClRightMonoidTerm A )  → ((ClRightMonoidTerm A )  → (ClRightMonoidTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClRightMonoidTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClRightMonoidTerm A ) → (Staged (ClRightMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpRightMonoidTerm n )  → ((OpRightMonoidTerm n )  → (OpRightMonoidTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpRightMonoidTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpRightMonoidTerm n ) → (Staged (OpRightMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightMonoidTerm2 n A )  → ((OpRightMonoidTerm2 n A )  → (OpRightMonoidTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpRightMonoidTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightMonoidTerm2 n A ) → (Staged (OpRightMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 