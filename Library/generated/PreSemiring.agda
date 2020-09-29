
 module PreSemiring  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PreSemiring (A  : Set )  : Set where
    constructor PreSemiringC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) )) 
  
  open PreSemiring
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
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) )) 
  
  record Hom (A1 A2  : Set ) (Pr1  : (PreSemiring A1 )) (Pr2  : (PreSemiring A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Pr1 ) x1 x2 ) ) ≡ ((* Pr2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Pr1 ) x1 x2 ) ) ≡ ((+ Pr2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Pr1  : (PreSemiring A1 )) (Pr2  : (PreSemiring A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Pr1 ) x1 x2 ) ((* Pr2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Pr1 ) x1 x2 ) ((+ Pr2 ) y1 y2 ) )))) 
  
  data PreSemiringTerm  : Set where
    *L : (PreSemiringTerm   → (PreSemiringTerm   → PreSemiringTerm  ))
    +L : (PreSemiringTerm   → (PreSemiringTerm   → PreSemiringTerm  )) 
  
  data ClPreSemiringTerm (A  : Set )  : Set where
    sing : (A  → (ClPreSemiringTerm A ) )
    *Cl : ((ClPreSemiringTerm A )  → ((ClPreSemiringTerm A )  → (ClPreSemiringTerm A ) ))
    +Cl : ((ClPreSemiringTerm A )  → ((ClPreSemiringTerm A )  → (ClPreSemiringTerm A ) )) 
  
  data OpPreSemiringTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPreSemiringTerm n ) )
    *OL : ((OpPreSemiringTerm n )  → ((OpPreSemiringTerm n )  → (OpPreSemiringTerm n ) ))
    +OL : ((OpPreSemiringTerm n )  → ((OpPreSemiringTerm n )  → (OpPreSemiringTerm n ) )) 
  
  data OpPreSemiringTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPreSemiringTerm2 n A ) )
    sing2 : (A  → (OpPreSemiringTerm2 n A ) )
    *OL2 : ((OpPreSemiringTerm2 n A )  → ((OpPreSemiringTerm2 n A )  → (OpPreSemiringTerm2 n A ) ))
    +OL2 : ((OpPreSemiringTerm2 n A )  → ((OpPreSemiringTerm2 n A )  → (OpPreSemiringTerm2 n A ) )) 
  
  simplifyB : (PreSemiringTerm  → PreSemiringTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClPreSemiringTerm A ) → (ClPreSemiringTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPreSemiringTerm n ) → (OpPreSemiringTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPreSemiringTerm2 n A ) → (OpPreSemiringTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PreSemiring A ) → (PreSemiringTerm  → A )))
  evalB Pr (*L x1 x2 )  = ((* Pr ) (evalB Pr x1 ) (evalB Pr x2 ) )
  
  evalB Pr (+L x1 x2 )  = ((+ Pr ) (evalB Pr x1 ) (evalB Pr x2 ) )
  
  evalCl : ({A  : Set }  → ((PreSemiring A ) → ((ClPreSemiringTerm A ) → A )))
  evalCl Pr (sing x1 )  = x1 
  
  evalCl Pr (*Cl x1 x2 )  = ((* Pr ) (evalCl Pr x1 ) (evalCl Pr x2 ) )
  
  evalCl Pr (+Cl x1 x2 )  = ((+ Pr ) (evalCl Pr x1 ) (evalCl Pr x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PreSemiring A ) → ((Vec A n ) → ((OpPreSemiringTerm n ) → A ))))
  evalOp n Pr vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Pr vars (*OL x1 x2 )  = ((* Pr ) (evalOp n Pr vars x1 ) (evalOp n Pr vars x2 ) )
  
  evalOp n Pr vars (+OL x1 x2 )  = ((+ Pr ) (evalOp n Pr vars x1 ) (evalOp n Pr vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PreSemiring A ) → ((Vec A n ) → ((OpPreSemiringTerm2 n A ) → A ))))
  evalOpE n Pr vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Pr vars (sing2 x1 )  = x1 
  
  evalOpE n Pr vars (*OL2 x1 x2 )  = ((* Pr ) (evalOpE n Pr vars x1 ) (evalOpE n Pr vars x2 ) )
  
  evalOpE n Pr vars (+OL2 x1 x2 )  = ((+ Pr ) (evalOpE n Pr vars x1 ) (evalOpE n Pr vars x2 ) )
  
  inductionB : ((P  : (PreSemiringTerm  → Set ))  → (((x1 x2  : PreSemiringTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : PreSemiringTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : PreSemiringTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClPreSemiringTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClPreSemiringTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClPreSemiringTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClPreSemiringTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpPreSemiringTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpPreSemiringTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpPreSemiringTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpPreSemiringTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPreSemiringTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpPreSemiringTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpPreSemiringTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpPreSemiringTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (PreSemiringTerm   → (PreSemiringTerm   → PreSemiringTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (PreSemiringTerm   → (PreSemiringTerm   → PreSemiringTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (PreSemiringTerm  → (Staged PreSemiringTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClPreSemiringTerm A )  → ((ClPreSemiringTerm A )  → (ClPreSemiringTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClPreSemiringTerm A )  → ((ClPreSemiringTerm A )  → (ClPreSemiringTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClPreSemiringTerm A ) → (Staged (ClPreSemiringTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpPreSemiringTerm n )  → ((OpPreSemiringTerm n )  → (OpPreSemiringTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpPreSemiringTerm n )  → ((OpPreSemiringTerm n )  → (OpPreSemiringTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpPreSemiringTerm n ) → (Staged (OpPreSemiringTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpPreSemiringTerm2 n A )  → ((OpPreSemiringTerm2 n A )  → (OpPreSemiringTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpPreSemiringTerm2 n A )  → ((OpPreSemiringTerm2 n A )  → (OpPreSemiringTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPreSemiringTerm2 n A ) → (Staged (OpPreSemiringTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
