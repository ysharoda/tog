
 module Absorption  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Absorption (A  : Set )  : Set where
    constructor AbsorptionC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      leftAbsorp_*_+ : ({x y  : A }  → (* x (+ x y ) ) ≡ x )
      leftAbsorp_+_* : ({x y  : A }  → (+ x (* x y ) ) ≡ x ) 
  
  open Absorption
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
      leftAbsorp_*_+P : ({xP yP  : (Prod AP AP )}  → (*P xP (+P xP yP ) ) ≡ xP )
      leftAbsorp_+_*P : ({xP yP  : (Prod AP AP )}  → (+P xP (*P xP yP ) ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Ab1  : (Absorption A1 )) (Ab2  : (Absorption A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ab1 ) x1 x2 ) ) ≡ ((* Ab2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ab1 ) x1 x2 ) ) ≡ ((+ Ab2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ab1  : (Absorption A1 )) (Ab2  : (Absorption A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ab1 ) x1 x2 ) ((* Ab2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ab1 ) x1 x2 ) ((+ Ab2 ) y1 y2 ) )))) 
  
  data AbsorptionTerm  : Set where
    *L : (AbsorptionTerm   → (AbsorptionTerm   → AbsorptionTerm  ))
    +L : (AbsorptionTerm   → (AbsorptionTerm   → AbsorptionTerm  )) 
  
  data ClAbsorptionTerm (A  : Set )  : Set where
    sing : (A  → (ClAbsorptionTerm A ) )
    *Cl : ((ClAbsorptionTerm A )  → ((ClAbsorptionTerm A )  → (ClAbsorptionTerm A ) ))
    +Cl : ((ClAbsorptionTerm A )  → ((ClAbsorptionTerm A )  → (ClAbsorptionTerm A ) )) 
  
  data OpAbsorptionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAbsorptionTerm n ) )
    *OL : ((OpAbsorptionTerm n )  → ((OpAbsorptionTerm n )  → (OpAbsorptionTerm n ) ))
    +OL : ((OpAbsorptionTerm n )  → ((OpAbsorptionTerm n )  → (OpAbsorptionTerm n ) )) 
  
  data OpAbsorptionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAbsorptionTerm2 n A ) )
    sing2 : (A  → (OpAbsorptionTerm2 n A ) )
    *OL2 : ((OpAbsorptionTerm2 n A )  → ((OpAbsorptionTerm2 n A )  → (OpAbsorptionTerm2 n A ) ))
    +OL2 : ((OpAbsorptionTerm2 n A )  → ((OpAbsorptionTerm2 n A )  → (OpAbsorptionTerm2 n A ) )) 
  
  simplifyB : (AbsorptionTerm  → AbsorptionTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAbsorptionTerm A ) → (ClAbsorptionTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAbsorptionTerm n ) → (OpAbsorptionTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAbsorptionTerm2 n A ) → (OpAbsorptionTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Absorption A ) → (AbsorptionTerm  → A )))
  evalB Ab (*L x1 x2 )  = ((* Ab ) (evalB Ab x1 ) (evalB Ab x2 ) )
  
  evalB Ab (+L x1 x2 )  = ((+ Ab ) (evalB Ab x1 ) (evalB Ab x2 ) )
  
  evalCl : ({A  : Set }  → ((Absorption A ) → ((ClAbsorptionTerm A ) → A )))
  evalCl Ab (sing x1 )  = x1 
  
  evalCl Ab (*Cl x1 x2 )  = ((* Ab ) (evalCl Ab x1 ) (evalCl Ab x2 ) )
  
  evalCl Ab (+Cl x1 x2 )  = ((+ Ab ) (evalCl Ab x1 ) (evalCl Ab x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Absorption A ) → ((Vec A n ) → ((OpAbsorptionTerm n ) → A ))))
  evalOp n Ab vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ab vars (*OL x1 x2 )  = ((* Ab ) (evalOp n Ab vars x1 ) (evalOp n Ab vars x2 ) )
  
  evalOp n Ab vars (+OL x1 x2 )  = ((+ Ab ) (evalOp n Ab vars x1 ) (evalOp n Ab vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Absorption A ) → ((Vec A n ) → ((OpAbsorptionTerm2 n A ) → A ))))
  evalOpE n Ab vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ab vars (sing2 x1 )  = x1 
  
  evalOpE n Ab vars (*OL2 x1 x2 )  = ((* Ab ) (evalOpE n Ab vars x1 ) (evalOpE n Ab vars x2 ) )
  
  evalOpE n Ab vars (+OL2 x1 x2 )  = ((+ Ab ) (evalOpE n Ab vars x1 ) (evalOpE n Ab vars x2 ) )
  
  inductionB : ((P  : (AbsorptionTerm  → Set ))  → (((x1 x2  : AbsorptionTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : AbsorptionTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : AbsorptionTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAbsorptionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAbsorptionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClAbsorptionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClAbsorptionTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAbsorptionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAbsorptionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpAbsorptionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpAbsorptionTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAbsorptionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAbsorptionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpAbsorptionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpAbsorptionTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (AbsorptionTerm   → (AbsorptionTerm   → AbsorptionTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (AbsorptionTerm   → (AbsorptionTerm   → AbsorptionTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (AbsorptionTerm  → (Staged AbsorptionTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClAbsorptionTerm A )  → ((ClAbsorptionTerm A )  → (ClAbsorptionTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClAbsorptionTerm A )  → ((ClAbsorptionTerm A )  → (ClAbsorptionTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAbsorptionTerm A ) → (Staged (ClAbsorptionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpAbsorptionTerm n )  → ((OpAbsorptionTerm n )  → (OpAbsorptionTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpAbsorptionTerm n )  → ((OpAbsorptionTerm n )  → (OpAbsorptionTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAbsorptionTerm n ) → (Staged (OpAbsorptionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpAbsorptionTerm2 n A )  → ((OpAbsorptionTerm2 n A )  → (OpAbsorptionTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAbsorptionTerm2 n A )  → ((OpAbsorptionTerm2 n A )  → (OpAbsorptionTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAbsorptionTerm2 n A ) → (Staged (OpAbsorptionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
