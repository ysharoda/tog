module Ringoid0Sig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Ringoid0Sig (A  : Set )  : Set where
    constructor Ringoid0SigC
    field
      0ᵢ : A 
      + : (A  → (A  → A ))
      * : (A  → (A  → A ))
  open Ringoid0Sig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS 
      +S : (AS  → (AS  → AS ))
      *S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP )
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
  record Hom (A1 A2  : Set ) (Ri1  : (Ringoid0Sig A1 )) (Ri2  : (Ringoid0Sig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Ri1 )  ) ≡ (0ᵢ Ri2 ) )
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ri1 ) x1 x2 ) ) ≡ ((+ Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ri1 ) x1 x2 ) ) ≡ ((* Ri2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ri1  : (Ringoid0Sig A1 )) (Ri2  : (Ringoid0Sig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Ri1 )  (0ᵢ Ri2 )  ))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ri1 ) x1 x2 ) ((+ Ri2 ) y1 y2 ) ))))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ri1 ) x1 x2 ) ((* Ri2 ) y1 y2 ) ))))
  data Ringoid0SigTerm  : Set where
    0L : Ringoid0SigTerm  
    +L : (Ringoid0SigTerm   → (Ringoid0SigTerm   → Ringoid0SigTerm  ))
    *L : (Ringoid0SigTerm   → (Ringoid0SigTerm   → Ringoid0SigTerm  ))
  data ClRingoid0SigTerm (A  : Set )  : Set where
    sing : (A  → (ClRingoid0SigTerm A ) )
    0Cl : (ClRingoid0SigTerm A ) 
    +Cl : ((ClRingoid0SigTerm A )  → ((ClRingoid0SigTerm A )  → (ClRingoid0SigTerm A ) ))
    *Cl : ((ClRingoid0SigTerm A )  → ((ClRingoid0SigTerm A )  → (ClRingoid0SigTerm A ) ))
  data OpRingoid0SigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRingoid0SigTerm n ) )
    0OL : (OpRingoid0SigTerm n ) 
    +OL : ((OpRingoid0SigTerm n )  → ((OpRingoid0SigTerm n )  → (OpRingoid0SigTerm n ) ))
    *OL : ((OpRingoid0SigTerm n )  → ((OpRingoid0SigTerm n )  → (OpRingoid0SigTerm n ) ))
  data OpRingoid0SigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRingoid0SigTerm2 n A ) )
    sing2 : (A  → (OpRingoid0SigTerm2 n A ) )
    0OL2 : (OpRingoid0SigTerm2 n A ) 
    +OL2 : ((OpRingoid0SigTerm2 n A )  → ((OpRingoid0SigTerm2 n A )  → (OpRingoid0SigTerm2 n A ) ))
    *OL2 : ((OpRingoid0SigTerm2 n A )  → ((OpRingoid0SigTerm2 n A )  → (OpRingoid0SigTerm2 n A ) ))
  evalB : ({A  : Set }  → ((Ringoid0Sig A ) → (Ringoid0SigTerm  → A )))
  evalB Ri 0L  = (0ᵢ Ri ) 
  
  evalB Ri (+L x1 x2 )  = ((+ Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (*L x1 x2 )  = ((* Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((Ringoid0Sig A ) → ((ClRingoid0SigTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri 0Cl  = (0ᵢ Ri ) 
  
  evalCl Ri (+Cl x1 x2 )  = ((+ Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (*Cl x1 x2 )  = ((* Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Ringoid0Sig A ) → ((Vec A n ) → ((OpRingoid0SigTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars 0OL  = (0ᵢ Ri ) 
  
  evalOp n Ri vars (+OL x1 x2 )  = ((+ Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (*OL x1 x2 )  = ((* Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Ringoid0Sig A ) → ((Vec A n ) → ((OpRingoid0SigTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars 0OL2  = (0ᵢ Ri ) 
  
  evalOpE n Ri vars (+OL2 x1 x2 )  = ((+ Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (*OL2 x1 x2 )  = ((* Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (Ringoid0SigTerm  → Set ))  → ((P 0L ) → (((x1 x2  : Ringoid0SigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1 x2  : Ringoid0SigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : Ringoid0SigTerm )  → (P x ))))))
  inductionB p p0l p+l p*l 0L  = p0l 
  
  inductionB p p0l p+l p*l (+L x1 x2 )  = (p+l _ _ (inductionB p p0l p+l p*l x1 ) (inductionB p p0l p+l p*l x2 ) )
  
  inductionB p p0l p+l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p0l p+l p*l x1 ) (inductionB p p0l p+l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRingoid0SigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClRingoid0SigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1 x2  : (ClRingoid0SigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClRingoid0SigTerm A ))  → (P x )))))))
  inductionCl _ p psing p0cl p+cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl p+cl p*cl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl p+cl p*cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p0cl p+cl p*cl x1 ) (inductionCl _ p psing p0cl p+cl p*cl x2 ) )
  
  inductionCl _ p psing p0cl p+cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p0cl p+cl p*cl x1 ) (inductionCl _ p psing p0cl p+cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRingoid0SigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpRingoid0SigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1 x2  : (OpRingoid0SigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpRingoid0SigTerm n ))  → (P x )))))))
  inductionOp _ p pv p0ol p+ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol p+ol p*ol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol p+ol p*ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p0ol p+ol p*ol x1 ) (inductionOp _ p pv p0ol p+ol p*ol x2 ) )
  
  inductionOp _ p pv p0ol p+ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p0ol p+ol p*ol x1 ) (inductionOp _ p pv p0ol p+ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRingoid0SigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpRingoid0SigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1 x2  : (OpRingoid0SigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpRingoid0SigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x2 ) )
  
  0L' : (  Ringoid0SigTerm  )
  0L'  = 0L 
  
  +L' : (  (Ringoid0SigTerm   → (Ringoid0SigTerm   → Ringoid0SigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  *L' : (  (Ringoid0SigTerm   → (Ringoid0SigTerm   → Ringoid0SigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (Ringoid0SigTerm  → (Staged Ringoid0SigTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClRingoid0SigTerm A ) )
  0Cl'  = 0Cl 
  
  +Cl' : ({A  : Set }  → ((ClRingoid0SigTerm A )  → ((ClRingoid0SigTerm A )  → (ClRingoid0SigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  *Cl' : ({A  : Set }  → ((ClRingoid0SigTerm A )  → ((ClRingoid0SigTerm A )  → (ClRingoid0SigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRingoid0SigTerm A ) → (Staged (ClRingoid0SigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpRingoid0SigTerm n ) )
  0OL'  = 0OL 
  
  +OL' : ({n  : Nat}  → ((OpRingoid0SigTerm n )  → ((OpRingoid0SigTerm n )  → (OpRingoid0SigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  *OL' : ({n  : Nat}  → ((OpRingoid0SigTerm n )  → ((OpRingoid0SigTerm n )  → (OpRingoid0SigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRingoid0SigTerm n ) → (Staged (OpRingoid0SigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpRingoid0SigTerm2 n A ) )
  0OL2'  = 0OL2 
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoid0SigTerm2 n A )  → ((OpRingoid0SigTerm2 n A )  → (OpRingoid0SigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoid0SigTerm2 n A )  → ((OpRingoid0SigTerm2 n A )  → (OpRingoid0SigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoid0SigTerm2 n A ) → (Staged (OpRingoid0SigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))