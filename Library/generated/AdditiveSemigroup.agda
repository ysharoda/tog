
 module AdditiveSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveSemigroup (A  : Set )  : Set where
    constructor AdditiveSemigroupC
    field
      + : (A  → (A  → A ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) )) 
  
  open AdditiveSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) )) 
  
  record Hom (A1 A2  : Set ) (Ad1  : (AdditiveSemigroup A1 )) (Ad2  : (AdditiveSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ad1 ) x1 x2 ) ) ≡ ((+ Ad2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ad1  : (AdditiveSemigroup A1 )) (Ad2  : (AdditiveSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ad1 ) x1 x2 ) ((+ Ad2 ) y1 y2 ) )))) 
  
  data AdditiveSemigroupTerm  : Set where
    +L : (AdditiveSemigroupTerm   → (AdditiveSemigroupTerm   → AdditiveSemigroupTerm  )) 
  
  data ClAdditiveSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClAdditiveSemigroupTerm A ) )
    +Cl : ((ClAdditiveSemigroupTerm A )  → ((ClAdditiveSemigroupTerm A )  → (ClAdditiveSemigroupTerm A ) )) 
  
  data OpAdditiveSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAdditiveSemigroupTerm n ) )
    +OL : ((OpAdditiveSemigroupTerm n )  → ((OpAdditiveSemigroupTerm n )  → (OpAdditiveSemigroupTerm n ) )) 
  
  data OpAdditiveSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAdditiveSemigroupTerm2 n A ) )
    sing2 : (A  → (OpAdditiveSemigroupTerm2 n A ) )
    +OL2 : ((OpAdditiveSemigroupTerm2 n A )  → ((OpAdditiveSemigroupTerm2 n A )  → (OpAdditiveSemigroupTerm2 n A ) )) 
  
  simplifyB : (AdditiveSemigroupTerm  → AdditiveSemigroupTerm )
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAdditiveSemigroupTerm A ) → (ClAdditiveSemigroupTerm A )))
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAdditiveSemigroupTerm n ) → (OpAdditiveSemigroupTerm n )))
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveSemigroupTerm2 n A ) → (OpAdditiveSemigroupTerm2 n A )))
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AdditiveSemigroup A ) → (AdditiveSemigroupTerm  → A )))
  evalB Ad (+L x1 x2 )  = ((+ Ad ) (evalB Ad x1 ) (evalB Ad x2 ) )
  
  evalCl : ({A  : Set }  → ((AdditiveSemigroup A ) → ((ClAdditiveSemigroupTerm A ) → A )))
  evalCl Ad (sing x1 )  = x1 
  
  evalCl Ad (+Cl x1 x2 )  = ((+ Ad ) (evalCl Ad x1 ) (evalCl Ad x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AdditiveSemigroup A ) → ((Vec A n ) → ((OpAdditiveSemigroupTerm n ) → A ))))
  evalOp n Ad vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ad vars (+OL x1 x2 )  = ((+ Ad ) (evalOp n Ad vars x1 ) (evalOp n Ad vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AdditiveSemigroup A ) → ((Vec A n ) → ((OpAdditiveSemigroupTerm2 n A ) → A ))))
  evalOpE n Ad vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ad vars (sing2 x1 )  = x1 
  
  evalOpE n Ad vars (+OL2 x1 x2 )  = ((+ Ad ) (evalOpE n Ad vars x1 ) (evalOpE n Ad vars x2 ) )
  
  inductionB : ((P  : (AdditiveSemigroupTerm  → Set ))  → (((x1 x2  : AdditiveSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : AdditiveSemigroupTerm )  → (P x ))))
  inductionB p p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l x1 ) (inductionB p p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAdditiveSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAdditiveSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClAdditiveSemigroupTerm A ))  → (P x )))))
  inductionCl _ p psing p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl x1 ) (inductionCl _ p psing p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAdditiveSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAdditiveSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpAdditiveSemigroupTerm n ))  → (P x )))))
  inductionOp _ p pv p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol x1 ) (inductionOp _ p pv p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAdditiveSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAdditiveSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpAdditiveSemigroupTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 x2 ) )
  
  +L' : (  (AdditiveSemigroupTerm   → (AdditiveSemigroupTerm   → AdditiveSemigroupTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (AdditiveSemigroupTerm  → (Staged AdditiveSemigroupTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClAdditiveSemigroupTerm A )  → ((ClAdditiveSemigroupTerm A )  → (ClAdditiveSemigroupTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAdditiveSemigroupTerm A ) → (Staged (ClAdditiveSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpAdditiveSemigroupTerm n )  → ((OpAdditiveSemigroupTerm n )  → (OpAdditiveSemigroupTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAdditiveSemigroupTerm n ) → (Staged (OpAdditiveSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveSemigroupTerm2 n A )  → ((OpAdditiveSemigroupTerm2 n A )  → (OpAdditiveSemigroupTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveSemigroupTerm2 n A ) → (Staged (OpAdditiveSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
