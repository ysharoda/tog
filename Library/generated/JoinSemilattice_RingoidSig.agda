
 module JoinSemilattice_RingoidSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record JoinSemilattice_RingoidSig (A  : Set )  : Set where
    constructor JoinSemilattice_RingoidSigC
    field
      + : (A  → (A  → A ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
      * : (A  → (A  → A )) 
  
  open JoinSemilattice_RingoidSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      *S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Jo1  : (JoinSemilattice_RingoidSig A1 )) (Jo2  : (JoinSemilattice_RingoidSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Jo1 ) x1 x2 ) ) ≡ ((+ Jo2 ) (hom x1 ) (hom x2 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Jo1 ) x1 x2 ) ) ≡ ((* Jo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Jo1  : (JoinSemilattice_RingoidSig A1 )) (Jo2  : (JoinSemilattice_RingoidSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Jo1 ) x1 x2 ) ((+ Jo2 ) y1 y2 ) ))))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Jo1 ) x1 x2 ) ((* Jo2 ) y1 y2 ) )))) 
  
  data JoinSemilattice_RingoidSigTerm  : Set where
    +L : (JoinSemilattice_RingoidSigTerm   → (JoinSemilattice_RingoidSigTerm   → JoinSemilattice_RingoidSigTerm  ))
    *L : (JoinSemilattice_RingoidSigTerm   → (JoinSemilattice_RingoidSigTerm   → JoinSemilattice_RingoidSigTerm  )) 
  
  data ClJoinSemilattice_RingoidSigTerm (A  : Set )  : Set where
    sing : (A  → (ClJoinSemilattice_RingoidSigTerm A ) )
    +Cl : ((ClJoinSemilattice_RingoidSigTerm A )  → ((ClJoinSemilattice_RingoidSigTerm A )  → (ClJoinSemilattice_RingoidSigTerm A ) ))
    *Cl : ((ClJoinSemilattice_RingoidSigTerm A )  → ((ClJoinSemilattice_RingoidSigTerm A )  → (ClJoinSemilattice_RingoidSigTerm A ) )) 
  
  data OpJoinSemilattice_RingoidSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpJoinSemilattice_RingoidSigTerm n ) )
    +OL : ((OpJoinSemilattice_RingoidSigTerm n )  → ((OpJoinSemilattice_RingoidSigTerm n )  → (OpJoinSemilattice_RingoidSigTerm n ) ))
    *OL : ((OpJoinSemilattice_RingoidSigTerm n )  → ((OpJoinSemilattice_RingoidSigTerm n )  → (OpJoinSemilattice_RingoidSigTerm n ) )) 
  
  data OpJoinSemilattice_RingoidSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpJoinSemilattice_RingoidSigTerm2 n A ) )
    sing2 : (A  → (OpJoinSemilattice_RingoidSigTerm2 n A ) )
    +OL2 : ((OpJoinSemilattice_RingoidSigTerm2 n A )  → ((OpJoinSemilattice_RingoidSigTerm2 n A )  → (OpJoinSemilattice_RingoidSigTerm2 n A ) ))
    *OL2 : ((OpJoinSemilattice_RingoidSigTerm2 n A )  → ((OpJoinSemilattice_RingoidSigTerm2 n A )  → (OpJoinSemilattice_RingoidSigTerm2 n A ) )) 
  
  simplifyB : (JoinSemilattice_RingoidSigTerm  → JoinSemilattice_RingoidSigTerm )
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClJoinSemilattice_RingoidSigTerm A ) → (ClJoinSemilattice_RingoidSigTerm A )))
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpJoinSemilattice_RingoidSigTerm n ) → (OpJoinSemilattice_RingoidSigTerm n )))
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpJoinSemilattice_RingoidSigTerm2 n A ) → (OpJoinSemilattice_RingoidSigTerm2 n A )))
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((JoinSemilattice_RingoidSig A ) → (JoinSemilattice_RingoidSigTerm  → A )))
  evalB Jo (+L x1 x2 )  = ((+ Jo ) (evalB Jo x1 ) (evalB Jo x2 ) )
  
  evalB Jo (*L x1 x2 )  = ((* Jo ) (evalB Jo x1 ) (evalB Jo x2 ) )
  
  evalCl : ({A  : Set }  → ((JoinSemilattice_RingoidSig A ) → ((ClJoinSemilattice_RingoidSigTerm A ) → A )))
  evalCl Jo (sing x1 )  = x1 
  
  evalCl Jo (+Cl x1 x2 )  = ((+ Jo ) (evalCl Jo x1 ) (evalCl Jo x2 ) )
  
  evalCl Jo (*Cl x1 x2 )  = ((* Jo ) (evalCl Jo x1 ) (evalCl Jo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((JoinSemilattice_RingoidSig A ) → ((Vec A n ) → ((OpJoinSemilattice_RingoidSigTerm n ) → A ))))
  evalOp n Jo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Jo vars (+OL x1 x2 )  = ((+ Jo ) (evalOp n Jo vars x1 ) (evalOp n Jo vars x2 ) )
  
  evalOp n Jo vars (*OL x1 x2 )  = ((* Jo ) (evalOp n Jo vars x1 ) (evalOp n Jo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((JoinSemilattice_RingoidSig A ) → ((Vec A n ) → ((OpJoinSemilattice_RingoidSigTerm2 n A ) → A ))))
  evalOpE n Jo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Jo vars (sing2 x1 )  = x1 
  
  evalOpE n Jo vars (+OL2 x1 x2 )  = ((+ Jo ) (evalOpE n Jo vars x1 ) (evalOpE n Jo vars x2 ) )
  
  evalOpE n Jo vars (*OL2 x1 x2 )  = ((* Jo ) (evalOpE n Jo vars x1 ) (evalOpE n Jo vars x2 ) )
  
  inductionB : ((P  : (JoinSemilattice_RingoidSigTerm  → Set ))  → (((x1 x2  : JoinSemilattice_RingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1 x2  : JoinSemilattice_RingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : JoinSemilattice_RingoidSigTerm )  → (P x )))))
  inductionB p p+l p*l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p*l x1 ) (inductionB p p+l p*l x2 ) )
  
  inductionB p p+l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p+l p*l x1 ) (inductionB p p+l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClJoinSemilattice_RingoidSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClJoinSemilattice_RingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1 x2  : (ClJoinSemilattice_RingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClJoinSemilattice_RingoidSigTerm A ))  → (P x ))))))
  inductionCl _ p psing p+cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p*cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p*cl x1 ) (inductionCl _ p psing p+cl p*cl x2 ) )
  
  inductionCl _ p psing p+cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p+cl p*cl x1 ) (inductionCl _ p psing p+cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpJoinSemilattice_RingoidSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpJoinSemilattice_RingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1 x2  : (OpJoinSemilattice_RingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpJoinSemilattice_RingoidSigTerm n ))  → (P x ))))))
  inductionOp _ p pv p+ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p*ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p*ol x1 ) (inductionOp _ p pv p+ol p*ol x2 ) )
  
  inductionOp _ p pv p+ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p+ol p*ol x1 ) (inductionOp _ p pv p+ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpJoinSemilattice_RingoidSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpJoinSemilattice_RingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1 x2  : (OpJoinSemilattice_RingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpJoinSemilattice_RingoidSigTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x2 ) )
  
  +L' : (  (JoinSemilattice_RingoidSigTerm   → (JoinSemilattice_RingoidSigTerm   → JoinSemilattice_RingoidSigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  *L' : (  (JoinSemilattice_RingoidSigTerm   → (JoinSemilattice_RingoidSigTerm   → JoinSemilattice_RingoidSigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (JoinSemilattice_RingoidSigTerm  → (Staged JoinSemilattice_RingoidSigTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClJoinSemilattice_RingoidSigTerm A )  → ((ClJoinSemilattice_RingoidSigTerm A )  → (ClJoinSemilattice_RingoidSigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  *Cl' : ({A  : Set }  → ((ClJoinSemilattice_RingoidSigTerm A )  → ((ClJoinSemilattice_RingoidSigTerm A )  → (ClJoinSemilattice_RingoidSigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClJoinSemilattice_RingoidSigTerm A ) → (Staged (ClJoinSemilattice_RingoidSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpJoinSemilattice_RingoidSigTerm n )  → ((OpJoinSemilattice_RingoidSigTerm n )  → (OpJoinSemilattice_RingoidSigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  *OL' : ({n  : Nat}  → ((OpJoinSemilattice_RingoidSigTerm n )  → ((OpJoinSemilattice_RingoidSigTerm n )  → (OpJoinSemilattice_RingoidSigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpJoinSemilattice_RingoidSigTerm n ) → (Staged (OpJoinSemilattice_RingoidSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpJoinSemilattice_RingoidSigTerm2 n A )  → ((OpJoinSemilattice_RingoidSigTerm2 n A )  → (OpJoinSemilattice_RingoidSigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpJoinSemilattice_RingoidSigTerm2 n A )  → ((OpJoinSemilattice_RingoidSigTerm2 n A )  → (OpJoinSemilattice_RingoidSigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpJoinSemilattice_RingoidSigTerm2 n A ) → (Staged (OpJoinSemilattice_RingoidSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
