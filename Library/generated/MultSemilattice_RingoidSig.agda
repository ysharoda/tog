
 module MultSemilattice_RingoidSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultSemilattice_RingoidSig (A  : Set )  : Set where
    constructor MultSemilattice_RingoidSigC
    field
      * : (A  → (A  → A ))
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      idempotent_* : ({x  : A }  → (* x x ) ≡ x )
      + : (A  → (A  → A )) 
  
  open MultSemilattice_RingoidSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      idempotent_*P : ({xP  : (Prod AP AP )}  → (*P xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Mu1  : (MultSemilattice_RingoidSig A1 )) (Mu2  : (MultSemilattice_RingoidSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Mu1 ) x1 x2 ) ) ≡ ((* Mu2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Mu1 ) x1 x2 ) ) ≡ ((+ Mu2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mu1  : (MultSemilattice_RingoidSig A1 )) (Mu2  : (MultSemilattice_RingoidSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Mu1 ) x1 x2 ) ((* Mu2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Mu1 ) x1 x2 ) ((+ Mu2 ) y1 y2 ) )))) 
  
  data MultSemilattice_RingoidSigTerm  : Set where
    *L : (MultSemilattice_RingoidSigTerm   → (MultSemilattice_RingoidSigTerm   → MultSemilattice_RingoidSigTerm  ))
    +L : (MultSemilattice_RingoidSigTerm   → (MultSemilattice_RingoidSigTerm   → MultSemilattice_RingoidSigTerm  )) 
  
  data ClMultSemilattice_RingoidSigTerm (A  : Set )  : Set where
    sing : (A  → (ClMultSemilattice_RingoidSigTerm A ) )
    *Cl : ((ClMultSemilattice_RingoidSigTerm A )  → ((ClMultSemilattice_RingoidSigTerm A )  → (ClMultSemilattice_RingoidSigTerm A ) ))
    +Cl : ((ClMultSemilattice_RingoidSigTerm A )  → ((ClMultSemilattice_RingoidSigTerm A )  → (ClMultSemilattice_RingoidSigTerm A ) )) 
  
  data OpMultSemilattice_RingoidSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMultSemilattice_RingoidSigTerm n ) )
    *OL : ((OpMultSemilattice_RingoidSigTerm n )  → ((OpMultSemilattice_RingoidSigTerm n )  → (OpMultSemilattice_RingoidSigTerm n ) ))
    +OL : ((OpMultSemilattice_RingoidSigTerm n )  → ((OpMultSemilattice_RingoidSigTerm n )  → (OpMultSemilattice_RingoidSigTerm n ) )) 
  
  data OpMultSemilattice_RingoidSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMultSemilattice_RingoidSigTerm2 n A ) )
    sing2 : (A  → (OpMultSemilattice_RingoidSigTerm2 n A ) )
    *OL2 : ((OpMultSemilattice_RingoidSigTerm2 n A )  → ((OpMultSemilattice_RingoidSigTerm2 n A )  → (OpMultSemilattice_RingoidSigTerm2 n A ) ))
    +OL2 : ((OpMultSemilattice_RingoidSigTerm2 n A )  → ((OpMultSemilattice_RingoidSigTerm2 n A )  → (OpMultSemilattice_RingoidSigTerm2 n A ) )) 
  
  simplifyB : (MultSemilattice_RingoidSigTerm  → MultSemilattice_RingoidSigTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMultSemilattice_RingoidSigTerm A ) → (ClMultSemilattice_RingoidSigTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMultSemilattice_RingoidSigTerm n ) → (OpMultSemilattice_RingoidSigTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMultSemilattice_RingoidSigTerm2 n A ) → (OpMultSemilattice_RingoidSigTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MultSemilattice_RingoidSig A ) → (MultSemilattice_RingoidSigTerm  → A )))
  evalB Mu (*L x1 x2 )  = ((* Mu ) (evalB Mu x1 ) (evalB Mu x2 ) )
  
  evalB Mu (+L x1 x2 )  = ((+ Mu ) (evalB Mu x1 ) (evalB Mu x2 ) )
  
  evalCl : ({A  : Set }  → ((MultSemilattice_RingoidSig A ) → ((ClMultSemilattice_RingoidSigTerm A ) → A )))
  evalCl Mu (sing x1 )  = x1 
  
  evalCl Mu (*Cl x1 x2 )  = ((* Mu ) (evalCl Mu x1 ) (evalCl Mu x2 ) )
  
  evalCl Mu (+Cl x1 x2 )  = ((+ Mu ) (evalCl Mu x1 ) (evalCl Mu x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MultSemilattice_RingoidSig A ) → ((Vec A n ) → ((OpMultSemilattice_RingoidSigTerm n ) → A ))))
  evalOp n Mu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mu vars (*OL x1 x2 )  = ((* Mu ) (evalOp n Mu vars x1 ) (evalOp n Mu vars x2 ) )
  
  evalOp n Mu vars (+OL x1 x2 )  = ((+ Mu ) (evalOp n Mu vars x1 ) (evalOp n Mu vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MultSemilattice_RingoidSig A ) → ((Vec A n ) → ((OpMultSemilattice_RingoidSigTerm2 n A ) → A ))))
  evalOpE n Mu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mu vars (sing2 x1 )  = x1 
  
  evalOpE n Mu vars (*OL2 x1 x2 )  = ((* Mu ) (evalOpE n Mu vars x1 ) (evalOpE n Mu vars x2 ) )
  
  evalOpE n Mu vars (+OL2 x1 x2 )  = ((+ Mu ) (evalOpE n Mu vars x1 ) (evalOpE n Mu vars x2 ) )
  
  inductionB : ((P  : (MultSemilattice_RingoidSigTerm  → Set ))  → (((x1 x2  : MultSemilattice_RingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : MultSemilattice_RingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : MultSemilattice_RingoidSigTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMultSemilattice_RingoidSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMultSemilattice_RingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClMultSemilattice_RingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClMultSemilattice_RingoidSigTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMultSemilattice_RingoidSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMultSemilattice_RingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpMultSemilattice_RingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpMultSemilattice_RingoidSigTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMultSemilattice_RingoidSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMultSemilattice_RingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpMultSemilattice_RingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpMultSemilattice_RingoidSigTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (MultSemilattice_RingoidSigTerm   → (MultSemilattice_RingoidSigTerm   → MultSemilattice_RingoidSigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (MultSemilattice_RingoidSigTerm   → (MultSemilattice_RingoidSigTerm   → MultSemilattice_RingoidSigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (MultSemilattice_RingoidSigTerm  → (Staged MultSemilattice_RingoidSigTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClMultSemilattice_RingoidSigTerm A )  → ((ClMultSemilattice_RingoidSigTerm A )  → (ClMultSemilattice_RingoidSigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClMultSemilattice_RingoidSigTerm A )  → ((ClMultSemilattice_RingoidSigTerm A )  → (ClMultSemilattice_RingoidSigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMultSemilattice_RingoidSigTerm A ) → (Staged (ClMultSemilattice_RingoidSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpMultSemilattice_RingoidSigTerm n )  → ((OpMultSemilattice_RingoidSigTerm n )  → (OpMultSemilattice_RingoidSigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpMultSemilattice_RingoidSigTerm n )  → ((OpMultSemilattice_RingoidSigTerm n )  → (OpMultSemilattice_RingoidSigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMultSemilattice_RingoidSigTerm n ) → (Staged (OpMultSemilattice_RingoidSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpMultSemilattice_RingoidSigTerm2 n A )  → ((OpMultSemilattice_RingoidSigTerm2 n A )  → (OpMultSemilattice_RingoidSigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpMultSemilattice_RingoidSigTerm2 n A )  → ((OpMultSemilattice_RingoidSigTerm2 n A )  → (OpMultSemilattice_RingoidSigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMultSemilattice_RingoidSigTerm2 n A ) → (Staged (OpMultSemilattice_RingoidSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
