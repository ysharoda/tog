
 module Ringoid1Sig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRingoid1Sig (A  : Set ) (*  : (A  → (A  → A ))) (1ᵢ  : A ) (+  : (A  → (A  → A )))  : Set where
    constructor IsRingoid1SigC
   
  
  record Ringoid1Sig (A  : Set )  : Set where
    constructor Ringoid1SigC
    field
      * : (A  → (A  → A ))
      1ᵢ : A 
      + : (A  → (A  → A ))
      isRingoid1Sig : (IsRingoid1Sig A (*) 1ᵢ (+) ) 
  
  open Ringoid1Sig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      1S : AS 
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (Ri1  : (Ringoid1Sig A1 )) (Ri2  : (Ringoid1Sig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ri1 ) x1 x2 ) ) ≡ ((* Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Ri1 )  ) ≡ (1ᵢ Ri2 ) )
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ri1 ) x1 x2 ) ) ≡ ((+ Ri2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ri1  : (Ringoid1Sig A1 )) (Ri2  : (Ringoid1Sig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ri1 ) x1 x2 ) ((* Ri2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Ri1 )  (1ᵢ Ri2 )  ))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ri1 ) x1 x2 ) ((+ Ri2 ) y1 y2 ) )))) 
  
  data Ringoid1SigTerm  : Set where
    *L : (Ringoid1SigTerm   → (Ringoid1SigTerm   → Ringoid1SigTerm  ))
    1L : Ringoid1SigTerm  
    +L : (Ringoid1SigTerm   → (Ringoid1SigTerm   → Ringoid1SigTerm  )) 
  
  data ClRingoid1SigTerm (A  : Set )  : Set where
    sing : (A  → (ClRingoid1SigTerm A ) )
    *Cl : ((ClRingoid1SigTerm A )  → ((ClRingoid1SigTerm A )  → (ClRingoid1SigTerm A ) ))
    1Cl : (ClRingoid1SigTerm A ) 
    +Cl : ((ClRingoid1SigTerm A )  → ((ClRingoid1SigTerm A )  → (ClRingoid1SigTerm A ) )) 
  
  data OpRingoid1SigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRingoid1SigTerm n ) )
    *OL : ((OpRingoid1SigTerm n )  → ((OpRingoid1SigTerm n )  → (OpRingoid1SigTerm n ) ))
    1OL : (OpRingoid1SigTerm n ) 
    +OL : ((OpRingoid1SigTerm n )  → ((OpRingoid1SigTerm n )  → (OpRingoid1SigTerm n ) )) 
  
  data OpRingoid1SigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRingoid1SigTerm2 n A ) )
    sing2 : (A  → (OpRingoid1SigTerm2 n A ) )
    *OL2 : ((OpRingoid1SigTerm2 n A )  → ((OpRingoid1SigTerm2 n A )  → (OpRingoid1SigTerm2 n A ) ))
    1OL2 : (OpRingoid1SigTerm2 n A ) 
    +OL2 : ((OpRingoid1SigTerm2 n A )  → ((OpRingoid1SigTerm2 n A )  → (OpRingoid1SigTerm2 n A ) )) 
  
  simplifyB : (Ringoid1SigTerm  → Ringoid1SigTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRingoid1SigTerm A ) → (ClRingoid1SigTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRingoid1SigTerm n ) → (OpRingoid1SigTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoid1SigTerm2 n A ) → (OpRingoid1SigTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Ringoid1Sig A ) → (Ringoid1SigTerm  → A )))
  evalB Ri (*L x1 x2 )  = ((* Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri 1L  = (1ᵢ Ri ) 
  
  evalB Ri (+L x1 x2 )  = ((+ Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((Ringoid1Sig A ) → ((ClRingoid1SigTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (*Cl x1 x2 )  = ((* Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri 1Cl  = (1ᵢ Ri ) 
  
  evalCl Ri (+Cl x1 x2 )  = ((+ Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Ringoid1Sig A ) → ((Vec A n ) → ((OpRingoid1SigTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (*OL x1 x2 )  = ((* Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars 1OL  = (1ᵢ Ri ) 
  
  evalOp n Ri vars (+OL x1 x2 )  = ((+ Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Ringoid1Sig A ) → ((Vec A n ) → ((OpRingoid1SigTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (*OL2 x1 x2 )  = ((* Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars 1OL2  = (1ᵢ Ri ) 
  
  evalOpE n Ri vars (+OL2 x1 x2 )  = ((+ Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (Ringoid1SigTerm  → Set ))  → (((x1 x2  : Ringoid1SigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P 1L ) → (((x1 x2  : Ringoid1SigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : Ringoid1SigTerm )  → (P x ))))))
  inductionB p p*l p1l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p1l p+l x1 ) (inductionB p p*l p1l p+l x2 ) )
  
  inductionB p p*l p1l p+l 1L  = p1l 
  
  inductionB p p*l p1l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p1l p+l x1 ) (inductionB p p*l p1l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRingoid1SigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRingoid1SigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P 1Cl ) → (((x1 x2  : (ClRingoid1SigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClRingoid1SigTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p1cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p1cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p1cl p+cl x1 ) (inductionCl _ p psing p*cl p1cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p1cl p+cl 1Cl  = p1cl 
  
  inductionCl _ p psing p*cl p1cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p1cl p+cl x1 ) (inductionCl _ p psing p*cl p1cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRingoid1SigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRingoid1SigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P 1OL ) → (((x1 x2  : (OpRingoid1SigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpRingoid1SigTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p1ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p1ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p1ol p+ol x1 ) (inductionOp _ p pv p*ol p1ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p1ol p+ol 1OL  = p1ol 
  
  inductionOp _ p pv p*ol p1ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p1ol p+ol x1 ) (inductionOp _ p pv p*ol p1ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRingoid1SigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRingoid1SigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P 1OL2 ) → (((x1 x2  : (OpRingoid1SigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpRingoid1SigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x2 ) )
  
  *L' : (  (Ringoid1SigTerm   → (Ringoid1SigTerm   → Ringoid1SigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  1L' : (  Ringoid1SigTerm  )
  1L'  = 1L 
  
  +L' : (  (Ringoid1SigTerm   → (Ringoid1SigTerm   → Ringoid1SigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (Ringoid1SigTerm  → (Staged Ringoid1SigTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClRingoid1SigTerm A )  → ((ClRingoid1SigTerm A )  → (ClRingoid1SigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClRingoid1SigTerm A ) )
  1Cl'  = 1Cl 
  
  +Cl' : ({A  : Set }  → ((ClRingoid1SigTerm A )  → ((ClRingoid1SigTerm A )  → (ClRingoid1SigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRingoid1SigTerm A ) → (Staged (ClRingoid1SigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpRingoid1SigTerm n )  → ((OpRingoid1SigTerm n )  → (OpRingoid1SigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpRingoid1SigTerm n ) )
  1OL'  = 1OL 
  
  +OL' : ({n  : Nat}  → ((OpRingoid1SigTerm n )  → ((OpRingoid1SigTerm n )  → (OpRingoid1SigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRingoid1SigTerm n ) → (Staged (OpRingoid1SigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoid1SigTerm2 n A )  → ((OpRingoid1SigTerm2 n A )  → (OpRingoid1SigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpRingoid1SigTerm2 n A ) )
  1OL2'  = 1OL2 
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoid1SigTerm2 n A )  → ((OpRingoid1SigTerm2 n A )  → (OpRingoid1SigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoid1SigTerm2 n A ) → (Staged (OpRingoid1SigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
