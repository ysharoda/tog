module JoinSemilattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record JoinSemilattice (A  : Set )  : Set where
    constructor JoinSemilatticeC
    field
      + : (A  → (A  → A ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
  open JoinSemilattice
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP )
  record Hom (A1 A2  : Set ) (Jo1  : (JoinSemilattice A1 )) (Jo2  : (JoinSemilattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Jo1 ) x1 x2 ) ) ≡ ((+ Jo2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Jo1  : (JoinSemilattice A1 )) (Jo2  : (JoinSemilattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Jo1 ) x1 x2 ) ((+ Jo2 ) y1 y2 ) ))))
  data JoinSemilatticeTerm  : Set where
    +L : (JoinSemilatticeTerm   → (JoinSemilatticeTerm   → JoinSemilatticeTerm  ))
  data ClJoinSemilatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClJoinSemilatticeTerm A ) )
    +Cl : ((ClJoinSemilatticeTerm A )  → ((ClJoinSemilatticeTerm A )  → (ClJoinSemilatticeTerm A ) ))
  data OpJoinSemilatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpJoinSemilatticeTerm n ) )
    +OL : ((OpJoinSemilatticeTerm n )  → ((OpJoinSemilatticeTerm n )  → (OpJoinSemilatticeTerm n ) ))
  data OpJoinSemilatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpJoinSemilatticeTerm2 n A ) )
    sing2 : (A  → (OpJoinSemilatticeTerm2 n A ) )
    +OL2 : ((OpJoinSemilatticeTerm2 n A )  → ((OpJoinSemilatticeTerm2 n A )  → (OpJoinSemilatticeTerm2 n A ) ))
  evalB : ({A  : Set }  → ((JoinSemilattice A ) → (JoinSemilatticeTerm  → A )))
  evalB Jo (+L x1 x2 )  = ((+ Jo ) (evalB Jo x1 ) (evalB Jo x2 ) )
  
  evalCl : ({A  : Set }  → ((JoinSemilattice A ) → ((ClJoinSemilatticeTerm A ) → A )))
  evalCl Jo (sing x1 )  = x1 
  
  evalCl Jo (+Cl x1 x2 )  = ((+ Jo ) (evalCl Jo x1 ) (evalCl Jo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((JoinSemilattice A ) → ((Vec A n ) → ((OpJoinSemilatticeTerm n ) → A ))))
  evalOp n Jo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Jo vars (+OL x1 x2 )  = ((+ Jo ) (evalOp n Jo vars x1 ) (evalOp n Jo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((JoinSemilattice A ) → ((Vec A n ) → ((OpJoinSemilatticeTerm2 n A ) → A ))))
  evalOpE n Jo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Jo vars (sing2 x1 )  = x1 
  
  evalOpE n Jo vars (+OL2 x1 x2 )  = ((+ Jo ) (evalOpE n Jo vars x1 ) (evalOpE n Jo vars x2 ) )
  
  inductionB : ((P  : (JoinSemilatticeTerm  → Set ))  → (((x1 x2  : JoinSemilatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : JoinSemilatticeTerm )  → (P x ))))
  inductionB p p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l x1 ) (inductionB p p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClJoinSemilatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClJoinSemilatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClJoinSemilatticeTerm A ))  → (P x )))))
  inductionCl _ p psing p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl x1 ) (inductionCl _ p psing p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpJoinSemilatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpJoinSemilatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpJoinSemilatticeTerm n ))  → (P x )))))
  inductionOp _ p pv p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol x1 ) (inductionOp _ p pv p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpJoinSemilatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpJoinSemilatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpJoinSemilatticeTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 x2 ) )
  
  +L' : (  (JoinSemilatticeTerm   → (JoinSemilatticeTerm   → JoinSemilatticeTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (JoinSemilatticeTerm  → (Staged JoinSemilatticeTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClJoinSemilatticeTerm A )  → ((ClJoinSemilatticeTerm A )  → (ClJoinSemilatticeTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClJoinSemilatticeTerm A ) → (Staged (ClJoinSemilatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpJoinSemilatticeTerm n )  → ((OpJoinSemilatticeTerm n )  → (OpJoinSemilatticeTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpJoinSemilatticeTerm n ) → (Staged (OpJoinSemilatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpJoinSemilatticeTerm2 n A )  → ((OpJoinSemilatticeTerm2 n A )  → (OpJoinSemilatticeTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpJoinSemilatticeTerm2 n A ) → (Staged (OpJoinSemilatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))