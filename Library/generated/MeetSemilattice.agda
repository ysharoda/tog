
 module MeetSemilattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MeetSemilattice (A  : Set )  : Set where
    constructor MeetSemilatticeC
    field
      op : (A  → (A  → A ))
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      idempotent_op : ({x  : A }  → (op x x ) ≡ x )
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x )) 
  
  open MeetSemilattice
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
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP )) 
  
  record Hom (A1 A2  : Set ) (Me1  : (MeetSemilattice A1 )) (Me2  : (MeetSemilattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Me1 ) x1 x2 ) ) ≡ ((op Me2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Me1  : (MeetSemilattice A1 )) (Me2  : (MeetSemilattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Me1 ) x1 x2 ) ((op Me2 ) y1 y2 ) )))) 
  
  data MeetSemilatticeTerm  : Set where
    opL : (MeetSemilatticeTerm   → (MeetSemilatticeTerm   → MeetSemilatticeTerm  )) 
  
  data ClMeetSemilatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClMeetSemilatticeTerm A ) )
    opCl : ((ClMeetSemilatticeTerm A )  → ((ClMeetSemilatticeTerm A )  → (ClMeetSemilatticeTerm A ) )) 
  
  data OpMeetSemilatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMeetSemilatticeTerm n ) )
    opOL : ((OpMeetSemilatticeTerm n )  → ((OpMeetSemilatticeTerm n )  → (OpMeetSemilatticeTerm n ) )) 
  
  data OpMeetSemilatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMeetSemilatticeTerm2 n A ) )
    sing2 : (A  → (OpMeetSemilatticeTerm2 n A ) )
    opOL2 : ((OpMeetSemilatticeTerm2 n A )  → ((OpMeetSemilatticeTerm2 n A )  → (OpMeetSemilatticeTerm2 n A ) )) 
  
  simplifyB : (MeetSemilatticeTerm  → MeetSemilatticeTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMeetSemilatticeTerm A ) → (ClMeetSemilatticeTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMeetSemilatticeTerm n ) → (OpMeetSemilatticeTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMeetSemilatticeTerm2 n A ) → (OpMeetSemilatticeTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MeetSemilattice A ) → (MeetSemilatticeTerm  → A )))
  evalB Me (opL x1 x2 )  = ((op Me ) (evalB Me x1 ) (evalB Me x2 ) )
  
  evalCl : ({A  : Set }  → ((MeetSemilattice A ) → ((ClMeetSemilatticeTerm A ) → A )))
  evalCl Me (sing x1 )  = x1 
  
  evalCl Me (opCl x1 x2 )  = ((op Me ) (evalCl Me x1 ) (evalCl Me x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MeetSemilattice A ) → ((Vec A n ) → ((OpMeetSemilatticeTerm n ) → A ))))
  evalOp n Me vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Me vars (opOL x1 x2 )  = ((op Me ) (evalOp n Me vars x1 ) (evalOp n Me vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MeetSemilattice A ) → ((Vec A n ) → ((OpMeetSemilatticeTerm2 n A ) → A ))))
  evalOpE n Me vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Me vars (sing2 x1 )  = x1 
  
  evalOpE n Me vars (opOL2 x1 x2 )  = ((op Me ) (evalOpE n Me vars x1 ) (evalOpE n Me vars x2 ) )
  
  inductionB : ((P  : (MeetSemilatticeTerm  → Set ))  → (((x1 x2  : MeetSemilatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : MeetSemilatticeTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMeetSemilatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMeetSemilatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClMeetSemilatticeTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMeetSemilatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMeetSemilatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpMeetSemilatticeTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMeetSemilatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMeetSemilatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpMeetSemilatticeTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (MeetSemilatticeTerm   → (MeetSemilatticeTerm   → MeetSemilatticeTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (MeetSemilatticeTerm  → (Staged MeetSemilatticeTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMeetSemilatticeTerm A )  → ((ClMeetSemilatticeTerm A )  → (ClMeetSemilatticeTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMeetSemilatticeTerm A ) → (Staged (ClMeetSemilatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMeetSemilatticeTerm n )  → ((OpMeetSemilatticeTerm n )  → (OpMeetSemilatticeTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMeetSemilatticeTerm n ) → (Staged (OpMeetSemilatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMeetSemilatticeTerm2 n A )  → ((OpMeetSemilatticeTerm2 n A )  → (OpMeetSemilatticeTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMeetSemilatticeTerm2 n A ) → (Staged (OpMeetSemilatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
