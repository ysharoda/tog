module MedialMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MedialMagma (A  : Set )  : Set where
    constructor MedialMagmaC
    field
      op : (A  → (A  → A ))
      mediates : ({w x y z  : A }  → (op (op x y ) (op z w ) ) ≡ (op (op x z ) (op y w ) ))
  open MedialMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      mediatesP : ({wP xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) (opP zP wP ) ) ≡ (opP (opP xP zP ) (opP yP wP ) ))
  record Hom (A1 A2  : Set ) (Me1  : (MedialMagma A1 )) (Me2  : (MedialMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Me1 ) x1 x2 ) ) ≡ ((op Me2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Me1  : (MedialMagma A1 )) (Me2  : (MedialMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Me1 ) x1 x2 ) ((op Me2 ) y1 y2 ) ))))
  data MedialMagmaTerm  : Set where
    opL : (MedialMagmaTerm   → (MedialMagmaTerm   → MedialMagmaTerm  ))
  data ClMedialMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClMedialMagmaTerm A ) )
    opCl : ((ClMedialMagmaTerm A )  → ((ClMedialMagmaTerm A )  → (ClMedialMagmaTerm A ) ))
  data OpMedialMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMedialMagmaTerm n ) )
    opOL : ((OpMedialMagmaTerm n )  → ((OpMedialMagmaTerm n )  → (OpMedialMagmaTerm n ) ))
  data OpMedialMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMedialMagmaTerm2 n A ) )
    sing2 : (A  → (OpMedialMagmaTerm2 n A ) )
    opOL2 : ((OpMedialMagmaTerm2 n A )  → ((OpMedialMagmaTerm2 n A )  → (OpMedialMagmaTerm2 n A ) ))
  evalB : ({A  : Set }  → ((MedialMagma A ) → (MedialMagmaTerm  → A )))
  evalB Me (opL x1 x2 )  = ((op Me ) (evalB Me x1 ) (evalB Me x2 ) )
  
  evalCl : ({A  : Set }  → ((MedialMagma A ) → ((ClMedialMagmaTerm A ) → A )))
  evalCl Me (sing x1 )  = x1 
  
  evalCl Me (opCl x1 x2 )  = ((op Me ) (evalCl Me x1 ) (evalCl Me x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MedialMagma A ) → ((Vec A n ) → ((OpMedialMagmaTerm n ) → A ))))
  evalOp n Me vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Me vars (opOL x1 x2 )  = ((op Me ) (evalOp n Me vars x1 ) (evalOp n Me vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MedialMagma A ) → ((Vec A n ) → ((OpMedialMagmaTerm2 n A ) → A ))))
  evalOpE n Me vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Me vars (sing2 x1 )  = x1 
  
  evalOpE n Me vars (opOL2 x1 x2 )  = ((op Me ) (evalOpE n Me vars x1 ) (evalOpE n Me vars x2 ) )
  
  inductionB : ((P  : (MedialMagmaTerm  → Set ))  → (((x1 x2  : MedialMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : MedialMagmaTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMedialMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMedialMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClMedialMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMedialMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMedialMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpMedialMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMedialMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMedialMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpMedialMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (MedialMagmaTerm   → (MedialMagmaTerm   → MedialMagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (MedialMagmaTerm  → (Staged MedialMagmaTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMedialMagmaTerm A )  → ((ClMedialMagmaTerm A )  → (ClMedialMagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMedialMagmaTerm A ) → (Staged (ClMedialMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMedialMagmaTerm n )  → ((OpMedialMagmaTerm n )  → (OpMedialMagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMedialMagmaTerm n ) → (Staged (OpMedialMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMedialMagmaTerm2 n A )  → ((OpMedialMagmaTerm2 n A )  → (OpMedialMagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMedialMagmaTerm2 n A ) → (Staged (OpMedialMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))