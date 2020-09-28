module Ringoid1  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Ringoid1 (A  : Set )  : Set where
    constructor Ringoid1C
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      1ᵢ : A 
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
  open Ringoid1
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
      1S : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
  record Hom (A1 A2  : Set ) (Ri1  : (Ringoid1 A1 )) (Ri2  : (Ringoid1 A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ri1 ) x1 x2 ) ) ≡ ((* Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ri1 ) x1 x2 ) ) ≡ ((+ Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Ri1 )  ) ≡ (1ᵢ Ri2 ) )
  record RelInterp (A1 A2  : Set ) (Ri1  : (Ringoid1 A1 )) (Ri2  : (Ringoid1 A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ri1 ) x1 x2 ) ((* Ri2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ri1 ) x1 x2 ) ((+ Ri2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Ri1 )  (1ᵢ Ri2 )  ))
  data Ringoid1LTerm  : Set where
    *L : (Ringoid1LTerm   → (Ringoid1LTerm   → Ringoid1LTerm  ))
    +L : (Ringoid1LTerm   → (Ringoid1LTerm   → Ringoid1LTerm  ))
    1L : Ringoid1LTerm  
  data ClRingoid1ClTerm (A  : Set )  : Set where
    sing : (A  → (ClRingoid1ClTerm A ) )
    *Cl : ((ClRingoid1ClTerm A )  → ((ClRingoid1ClTerm A )  → (ClRingoid1ClTerm A ) ))
    +Cl : ((ClRingoid1ClTerm A )  → ((ClRingoid1ClTerm A )  → (ClRingoid1ClTerm A ) ))
    1Cl : (ClRingoid1ClTerm A ) 
  data OpRingoid1OLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRingoid1OLTerm n ) )
    *OL : ((OpRingoid1OLTerm n )  → ((OpRingoid1OLTerm n )  → (OpRingoid1OLTerm n ) ))
    +OL : ((OpRingoid1OLTerm n )  → ((OpRingoid1OLTerm n )  → (OpRingoid1OLTerm n ) ))
    1OL : (OpRingoid1OLTerm n ) 
  data OpRingoid1OL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRingoid1OL2Term2 n A ) )
    sing2 : (A  → (OpRingoid1OL2Term2 n A ) )
    *OL2 : ((OpRingoid1OL2Term2 n A )  → ((OpRingoid1OL2Term2 n A )  → (OpRingoid1OL2Term2 n A ) ))
    +OL2 : ((OpRingoid1OL2Term2 n A )  → ((OpRingoid1OL2Term2 n A )  → (OpRingoid1OL2Term2 n A ) ))
    1OL2 : (OpRingoid1OL2Term2 n A ) 
  evalB : ({A  : Set }  → ((Ringoid1 A ) → (Ringoid1LTerm  → A )))
  evalB Ri (*L x1 x2 )  = ((* Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (+L x1 x2 )  = ((+ Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri 1L  = (1ᵢ Ri ) 
  
  evalCl : ({A  : Set }  → ((Ringoid1 A ) → ((ClRingoid1ClTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (*Cl x1 x2 )  = ((* Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (+Cl x1 x2 )  = ((+ Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri 1Cl  = (1ᵢ Ri ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Ringoid1 A ) → ((Vec A n ) → ((OpRingoid1OLTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (*OL x1 x2 )  = ((* Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (+OL x1 x2 )  = ((+ Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars 1OL  = (1ᵢ Ri ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Ringoid1 A ) → ((Vec A n ) → ((OpRingoid1OL2Term2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (*OL2 x1 x2 )  = ((* Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (+OL2 x1 x2 )  = ((+ Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars 1OL2  = (1ᵢ Ri ) 
  
  inductionB : ((P  : (Ringoid1LTerm  → Set ))  → (((x1 x2  : Ringoid1LTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : Ringoid1LTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 1L ) → ((x  : Ringoid1LTerm )  → (P x ))))))
  inductionB p p*l p+l p1l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l p1l x1 ) (inductionB p p*l p+l p1l x2 ) )
  
  inductionB p p*l p+l p1l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l p1l x1 ) (inductionB p p*l p+l p1l x2 ) )
  
  inductionB p p*l p+l p1l 1L  = p1l 
  
  inductionCl : ((A  : Set ) (P  : ((ClRingoid1ClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRingoid1ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClRingoid1ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 1Cl ) → ((x  : (ClRingoid1ClTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p+cl p1cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl p1cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl p1cl x1 ) (inductionCl _ p psing p*cl p+cl p1cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl p1cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl p1cl x1 ) (inductionCl _ p psing p*cl p+cl p1cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl p1cl 1Cl  = p1cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpRingoid1OLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRingoid1OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpRingoid1OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 1OL ) → ((x  : (OpRingoid1OLTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p+ol p1ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol p1ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol p1ol x1 ) (inductionOp _ p pv p*ol p+ol p1ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol p1ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol p1ol x1 ) (inductionOp _ p pv p*ol p+ol p1ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol p1ol 1OL  = p1ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRingoid1OL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRingoid1OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpRingoid1OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 1OL2 ) → ((x  : (OpRingoid1OL2Term2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 1OL2  = p1ol2 
  
  *L' : (  (Ringoid1LTerm   → (Ringoid1LTerm   → Ringoid1LTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (Ringoid1LTerm   → (Ringoid1LTerm   → Ringoid1LTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  1L' : (  Ringoid1LTerm  )
  1L'  = 1L 
  
  stageB : (Ringoid1LTerm  → (Staged Ringoid1LTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  *Cl' : ({A  : Set }  → ((ClRingoid1ClTerm A )  → ((ClRingoid1ClTerm A )  → (ClRingoid1ClTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClRingoid1ClTerm A )  → ((ClRingoid1ClTerm A )  → (ClRingoid1ClTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClRingoid1ClTerm A ) )
  1Cl'  = 1Cl 
  
  stageCl : ((A  : Set )  → ((ClRingoid1ClTerm A ) → (Staged (ClRingoid1ClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  *OL' : ({n  : Nat}  → ((OpRingoid1OLTerm n )  → ((OpRingoid1OLTerm n )  → (OpRingoid1OLTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpRingoid1OLTerm n )  → ((OpRingoid1OLTerm n )  → (OpRingoid1OLTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpRingoid1OLTerm n ) )
  1OL'  = 1OL 
  
  stageOp : ((n  : Nat)  → ((OpRingoid1OLTerm n ) → (Staged (OpRingoid1OLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoid1OL2Term2 n A )  → ((OpRingoid1OL2Term2 n A )  → (OpRingoid1OL2Term2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoid1OL2Term2 n A )  → ((OpRingoid1OL2Term2 n A )  → (OpRingoid1OL2Term2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpRingoid1OL2Term2 n A ) )
  1OL2'  = 1OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoid1OL2Term2 n A ) → (Staged (OpRingoid1OL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 