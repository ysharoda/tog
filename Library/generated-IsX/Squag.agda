
 module Squag  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsSquag (A  : Set ) (op  : (A  → (A  → A )))  : Set where
    constructor IsSquagC
    field
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x ))
      antiAbsorbent : ({x y  : A }  → (op x (op x y ) ) ≡ y )
      idempotent_op : ({x  : A }  → (op x x ) ≡ x ) 
  
  record Squag (A  : Set )  : Set where
    constructor SquagC
    field
      op : (A  → (A  → A ))
      isSquag : (IsSquag A op ) 
  
  open Squag
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP ))
      antiAbsorbentP : ({xP yP  : (Prod AP AP )}  → (opP xP (opP xP yP ) ) ≡ yP )
      idempotent_opP : ({xP  : (Prod AP AP )}  → (opP xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Sq1  : (Squag A1 )) (Sq2  : (Squag A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Sq1 ) x1 x2 ) ) ≡ ((op Sq2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Sq1  : (Squag A1 )) (Sq2  : (Squag A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Sq1 ) x1 x2 ) ((op Sq2 ) y1 y2 ) )))) 
  
  data SquagTerm  : Set where
    opL : (SquagTerm   → (SquagTerm   → SquagTerm  )) 
  
  data ClSquagTerm (A  : Set )  : Set where
    sing : (A  → (ClSquagTerm A ) )
    opCl : ((ClSquagTerm A )  → ((ClSquagTerm A )  → (ClSquagTerm A ) )) 
  
  data OpSquagTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpSquagTerm n ) )
    opOL : ((OpSquagTerm n )  → ((OpSquagTerm n )  → (OpSquagTerm n ) )) 
  
  data OpSquagTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpSquagTerm2 n A ) )
    sing2 : (A  → (OpSquagTerm2 n A ) )
    opOL2 : ((OpSquagTerm2 n A )  → ((OpSquagTerm2 n A )  → (OpSquagTerm2 n A ) )) 
  
  simplifyB : (SquagTerm  → SquagTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClSquagTerm A ) → (ClSquagTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpSquagTerm n ) → (OpSquagTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpSquagTerm2 n A ) → (OpSquagTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Squag A ) → (SquagTerm  → A )))
  evalB Sq (opL x1 x2 )  = ((op Sq ) (evalB Sq x1 ) (evalB Sq x2 ) )
  
  evalCl : ({A  : Set }  → ((Squag A ) → ((ClSquagTerm A ) → A )))
  evalCl Sq (sing x1 )  = x1 
  
  evalCl Sq (opCl x1 x2 )  = ((op Sq ) (evalCl Sq x1 ) (evalCl Sq x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Squag A ) → ((Vec A n ) → ((OpSquagTerm n ) → A ))))
  evalOp n Sq vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Sq vars (opOL x1 x2 )  = ((op Sq ) (evalOp n Sq vars x1 ) (evalOp n Sq vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Squag A ) → ((Vec A n ) → ((OpSquagTerm2 n A ) → A ))))
  evalOpE n Sq vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Sq vars (sing2 x1 )  = x1 
  
  evalOpE n Sq vars (opOL2 x1 x2 )  = ((op Sq ) (evalOpE n Sq vars x1 ) (evalOpE n Sq vars x2 ) )
  
  inductionB : ((P  : (SquagTerm  → Set ))  → (((x1 x2  : SquagTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : SquagTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClSquagTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClSquagTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClSquagTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpSquagTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpSquagTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpSquagTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpSquagTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpSquagTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpSquagTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (SquagTerm   → (SquagTerm   → SquagTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (SquagTerm  → (Staged SquagTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClSquagTerm A )  → ((ClSquagTerm A )  → (ClSquagTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClSquagTerm A ) → (Staged (ClSquagTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpSquagTerm n )  → ((OpSquagTerm n )  → (OpSquagTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpSquagTerm n ) → (Staged (OpSquagTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpSquagTerm2 n A )  → ((OpSquagTerm2 n A )  → (OpSquagTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpSquagTerm2 n A ) → (Staged (OpSquagTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
