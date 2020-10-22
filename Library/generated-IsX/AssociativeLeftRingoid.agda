
 module AssociativeLeftRingoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAssociativeLeftRingoid (A  : Set ) (*  : (A  → (A  → A ))) (+  : (A  → (A  → A )))  : Set where
    constructor IsAssociativeLeftRingoidC
    field
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) )) 
  
  record AssociativeLeftRingoid (A  : Set )  : Set where
    constructor AssociativeLeftRingoidC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      isAssociativeLeftRingoid : (IsAssociativeLeftRingoid A (*) (+) ) 
  
  open AssociativeLeftRingoid
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
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) )) 
  
  record Hom (A1 A2  : Set ) (As1  : (AssociativeLeftRingoid A1 )) (As2  : (AssociativeLeftRingoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* As1 ) x1 x2 ) ) ≡ ((* As2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ As1 ) x1 x2 ) ) ≡ ((+ As2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (As1  : (AssociativeLeftRingoid A1 )) (As2  : (AssociativeLeftRingoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* As1 ) x1 x2 ) ((* As2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ As1 ) x1 x2 ) ((+ As2 ) y1 y2 ) )))) 
  
  data AssociativeLeftRingoidTerm  : Set where
    *L : (AssociativeLeftRingoidTerm   → (AssociativeLeftRingoidTerm   → AssociativeLeftRingoidTerm  ))
    +L : (AssociativeLeftRingoidTerm   → (AssociativeLeftRingoidTerm   → AssociativeLeftRingoidTerm  )) 
  
  data ClAssociativeLeftRingoidTerm (A  : Set )  : Set where
    sing : (A  → (ClAssociativeLeftRingoidTerm A ) )
    *Cl : ((ClAssociativeLeftRingoidTerm A )  → ((ClAssociativeLeftRingoidTerm A )  → (ClAssociativeLeftRingoidTerm A ) ))
    +Cl : ((ClAssociativeLeftRingoidTerm A )  → ((ClAssociativeLeftRingoidTerm A )  → (ClAssociativeLeftRingoidTerm A ) )) 
  
  data OpAssociativeLeftRingoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAssociativeLeftRingoidTerm n ) )
    *OL : ((OpAssociativeLeftRingoidTerm n )  → ((OpAssociativeLeftRingoidTerm n )  → (OpAssociativeLeftRingoidTerm n ) ))
    +OL : ((OpAssociativeLeftRingoidTerm n )  → ((OpAssociativeLeftRingoidTerm n )  → (OpAssociativeLeftRingoidTerm n ) )) 
  
  data OpAssociativeLeftRingoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAssociativeLeftRingoidTerm2 n A ) )
    sing2 : (A  → (OpAssociativeLeftRingoidTerm2 n A ) )
    *OL2 : ((OpAssociativeLeftRingoidTerm2 n A )  → ((OpAssociativeLeftRingoidTerm2 n A )  → (OpAssociativeLeftRingoidTerm2 n A ) ))
    +OL2 : ((OpAssociativeLeftRingoidTerm2 n A )  → ((OpAssociativeLeftRingoidTerm2 n A )  → (OpAssociativeLeftRingoidTerm2 n A ) )) 
  
  simplifyB : (AssociativeLeftRingoidTerm  → AssociativeLeftRingoidTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAssociativeLeftRingoidTerm A ) → (ClAssociativeLeftRingoidTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAssociativeLeftRingoidTerm n ) → (OpAssociativeLeftRingoidTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAssociativeLeftRingoidTerm2 n A ) → (OpAssociativeLeftRingoidTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AssociativeLeftRingoid A ) → (AssociativeLeftRingoidTerm  → A )))
  evalB As (*L x1 x2 )  = ((* As ) (evalB As x1 ) (evalB As x2 ) )
  
  evalB As (+L x1 x2 )  = ((+ As ) (evalB As x1 ) (evalB As x2 ) )
  
  evalCl : ({A  : Set }  → ((AssociativeLeftRingoid A ) → ((ClAssociativeLeftRingoidTerm A ) → A )))
  evalCl As (sing x1 )  = x1 
  
  evalCl As (*Cl x1 x2 )  = ((* As ) (evalCl As x1 ) (evalCl As x2 ) )
  
  evalCl As (+Cl x1 x2 )  = ((+ As ) (evalCl As x1 ) (evalCl As x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AssociativeLeftRingoid A ) → ((Vec A n ) → ((OpAssociativeLeftRingoidTerm n ) → A ))))
  evalOp n As vars (v x1 )  = (lookup vars x1 )
  
  evalOp n As vars (*OL x1 x2 )  = ((* As ) (evalOp n As vars x1 ) (evalOp n As vars x2 ) )
  
  evalOp n As vars (+OL x1 x2 )  = ((+ As ) (evalOp n As vars x1 ) (evalOp n As vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AssociativeLeftRingoid A ) → ((Vec A n ) → ((OpAssociativeLeftRingoidTerm2 n A ) → A ))))
  evalOpE n As vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n As vars (sing2 x1 )  = x1 
  
  evalOpE n As vars (*OL2 x1 x2 )  = ((* As ) (evalOpE n As vars x1 ) (evalOpE n As vars x2 ) )
  
  evalOpE n As vars (+OL2 x1 x2 )  = ((+ As ) (evalOpE n As vars x1 ) (evalOpE n As vars x2 ) )
  
  inductionB : ((P  : (AssociativeLeftRingoidTerm  → Set ))  → (((x1 x2  : AssociativeLeftRingoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : AssociativeLeftRingoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : AssociativeLeftRingoidTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAssociativeLeftRingoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAssociativeLeftRingoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClAssociativeLeftRingoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClAssociativeLeftRingoidTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAssociativeLeftRingoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAssociativeLeftRingoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpAssociativeLeftRingoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpAssociativeLeftRingoidTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAssociativeLeftRingoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAssociativeLeftRingoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpAssociativeLeftRingoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpAssociativeLeftRingoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (AssociativeLeftRingoidTerm   → (AssociativeLeftRingoidTerm   → AssociativeLeftRingoidTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (AssociativeLeftRingoidTerm   → (AssociativeLeftRingoidTerm   → AssociativeLeftRingoidTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (AssociativeLeftRingoidTerm  → (Staged AssociativeLeftRingoidTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClAssociativeLeftRingoidTerm A )  → ((ClAssociativeLeftRingoidTerm A )  → (ClAssociativeLeftRingoidTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClAssociativeLeftRingoidTerm A )  → ((ClAssociativeLeftRingoidTerm A )  → (ClAssociativeLeftRingoidTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAssociativeLeftRingoidTerm A ) → (Staged (ClAssociativeLeftRingoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpAssociativeLeftRingoidTerm n )  → ((OpAssociativeLeftRingoidTerm n )  → (OpAssociativeLeftRingoidTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpAssociativeLeftRingoidTerm n )  → ((OpAssociativeLeftRingoidTerm n )  → (OpAssociativeLeftRingoidTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAssociativeLeftRingoidTerm n ) → (Staged (OpAssociativeLeftRingoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpAssociativeLeftRingoidTerm2 n A )  → ((OpAssociativeLeftRingoidTerm2 n A )  → (OpAssociativeLeftRingoidTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAssociativeLeftRingoidTerm2 n A )  → ((OpAssociativeLeftRingoidTerm2 n A )  → (OpAssociativeLeftRingoidTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAssociativeLeftRingoidTerm2 n A ) → (Staged (OpAssociativeLeftRingoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
