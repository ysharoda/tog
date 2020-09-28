module LeftRingoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftRingoid (A  : Set )  : Set where
    constructor LeftRingoidC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
  open LeftRingoid
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
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
  record Hom (A1 A2  : Set ) (Le1  : (LeftRingoid A1 )) (Le2  : (LeftRingoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Le1 ) x1 x2 ) ) ≡ ((* Le2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Le1 ) x1 x2 ) ) ≡ ((+ Le2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftRingoid A1 )) (Le2  : (LeftRingoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Le1 ) x1 x2 ) ((* Le2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Le1 ) x1 x2 ) ((+ Le2 ) y1 y2 ) ))))
  data LeftRingoidTerm  : Set where
    *L : (LeftRingoidTerm   → (LeftRingoidTerm   → LeftRingoidTerm  ))
    +L : (LeftRingoidTerm   → (LeftRingoidTerm   → LeftRingoidTerm  ))
  data ClLeftRingoidTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftRingoidTerm A ) )
    *Cl : ((ClLeftRingoidTerm A )  → ((ClLeftRingoidTerm A )  → (ClLeftRingoidTerm A ) ))
    +Cl : ((ClLeftRingoidTerm A )  → ((ClLeftRingoidTerm A )  → (ClLeftRingoidTerm A ) ))
  data OpLeftRingoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftRingoidTerm n ) )
    *OL : ((OpLeftRingoidTerm n )  → ((OpLeftRingoidTerm n )  → (OpLeftRingoidTerm n ) ))
    +OL : ((OpLeftRingoidTerm n )  → ((OpLeftRingoidTerm n )  → (OpLeftRingoidTerm n ) ))
  data OpLeftRingoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftRingoidTerm2 n A ) )
    sing2 : (A  → (OpLeftRingoidTerm2 n A ) )
    *OL2 : ((OpLeftRingoidTerm2 n A )  → ((OpLeftRingoidTerm2 n A )  → (OpLeftRingoidTerm2 n A ) ))
    +OL2 : ((OpLeftRingoidTerm2 n A )  → ((OpLeftRingoidTerm2 n A )  → (OpLeftRingoidTerm2 n A ) ))
  evalB : ({A  : Set }  → ((LeftRingoid A ) → (LeftRingoidTerm  → A )))
  evalB Le (*L x1 x2 )  = ((* Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalB Le (+L x1 x2 )  = ((+ Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftRingoid A ) → ((ClLeftRingoidTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (*Cl x1 x2 )  = ((* Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalCl Le (+Cl x1 x2 )  = ((+ Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftRingoid A ) → ((Vec A n ) → ((OpLeftRingoidTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (*OL x1 x2 )  = ((* Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOp n Le vars (+OL x1 x2 )  = ((+ Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftRingoid A ) → ((Vec A n ) → ((OpLeftRingoidTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (*OL2 x1 x2 )  = ((* Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  evalOpE n Le vars (+OL2 x1 x2 )  = ((+ Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftRingoidTerm  → Set ))  → (((x1 x2  : LeftRingoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : LeftRingoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : LeftRingoidTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftRingoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftRingoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClLeftRingoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClLeftRingoidTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftRingoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftRingoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpLeftRingoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpLeftRingoidTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftRingoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftRingoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpLeftRingoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpLeftRingoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (LeftRingoidTerm   → (LeftRingoidTerm   → LeftRingoidTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (LeftRingoidTerm   → (LeftRingoidTerm   → LeftRingoidTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (LeftRingoidTerm  → (Staged LeftRingoidTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClLeftRingoidTerm A )  → ((ClLeftRingoidTerm A )  → (ClLeftRingoidTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClLeftRingoidTerm A )  → ((ClLeftRingoidTerm A )  → (ClLeftRingoidTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftRingoidTerm A ) → (Staged (ClLeftRingoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpLeftRingoidTerm n )  → ((OpLeftRingoidTerm n )  → (OpLeftRingoidTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpLeftRingoidTerm n )  → ((OpLeftRingoidTerm n )  → (OpLeftRingoidTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftRingoidTerm n ) → (Staged (OpLeftRingoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpLeftRingoidTerm2 n A )  → ((OpLeftRingoidTerm2 n A )  → (OpLeftRingoidTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpLeftRingoidTerm2 n A )  → ((OpLeftRingoidTerm2 n A )  → (OpLeftRingoidTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftRingoidTerm2 n A ) → (Staged (OpLeftRingoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))