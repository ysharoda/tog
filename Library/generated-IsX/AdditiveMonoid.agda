
 module AdditiveMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAdditiveMonoid (A  : Set ) (0ᵢ  : A ) (+  : (A  → (A  → A )))  : Set where
    constructor IsAdditiveMonoidC
    field
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) )) 
  
  record AdditiveMonoid (A  : Set )  : Set where
    constructor AdditiveMonoidC
    field
      0ᵢ : A 
      + : (A  → (A  → A ))
      isAdditiveMonoid : (IsAdditiveMonoid A 0ᵢ (+) ) 
  
  open AdditiveMonoid
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS 
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP )
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) )) 
  
  record Hom (A1 A2  : Set ) (Ad1  : (AdditiveMonoid A1 )) (Ad2  : (AdditiveMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Ad1 )  ) ≡ (0ᵢ Ad2 ) )
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ad1 ) x1 x2 ) ) ≡ ((+ Ad2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ad1  : (AdditiveMonoid A1 )) (Ad2  : (AdditiveMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Ad1 )  (0ᵢ Ad2 )  ))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ad1 ) x1 x2 ) ((+ Ad2 ) y1 y2 ) )))) 
  
  data AdditiveMonoidTerm  : Set where
    0L : AdditiveMonoidTerm  
    +L : (AdditiveMonoidTerm   → (AdditiveMonoidTerm   → AdditiveMonoidTerm  )) 
  
  data ClAdditiveMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClAdditiveMonoidTerm A ) )
    0Cl : (ClAdditiveMonoidTerm A ) 
    +Cl : ((ClAdditiveMonoidTerm A )  → ((ClAdditiveMonoidTerm A )  → (ClAdditiveMonoidTerm A ) )) 
  
  data OpAdditiveMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAdditiveMonoidTerm n ) )
    0OL : (OpAdditiveMonoidTerm n ) 
    +OL : ((OpAdditiveMonoidTerm n )  → ((OpAdditiveMonoidTerm n )  → (OpAdditiveMonoidTerm n ) )) 
  
  data OpAdditiveMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAdditiveMonoidTerm2 n A ) )
    sing2 : (A  → (OpAdditiveMonoidTerm2 n A ) )
    0OL2 : (OpAdditiveMonoidTerm2 n A ) 
    +OL2 : ((OpAdditiveMonoidTerm2 n A )  → ((OpAdditiveMonoidTerm2 n A )  → (OpAdditiveMonoidTerm2 n A ) )) 
  
  simplifyB : (AdditiveMonoidTerm  → AdditiveMonoidTerm )
  simplifyB (+L 0L x )  = x 
  
  simplifyB (+L x 0L )  = x 
  
  simplifyB 0L  = 0L 
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAdditiveMonoidTerm A ) → (ClAdditiveMonoidTerm A )))
  simplifyCl _ (+Cl 0Cl x )  = x 
  
  simplifyCl _ (+Cl x 0Cl )  = x 
  
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAdditiveMonoidTerm n ) → (OpAdditiveMonoidTerm n )))
  simplifyOp _ (+OL 0OL x )  = x 
  
  simplifyOp _ (+OL x 0OL )  = x 
  
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveMonoidTerm2 n A ) → (OpAdditiveMonoidTerm2 n A )))
  simplifyOpE _ _ (+OL2 0OL2 x )  = x 
  
  simplifyOpE _ _ (+OL2 x 0OL2 )  = x 
  
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AdditiveMonoid A ) → (AdditiveMonoidTerm  → A )))
  evalB Ad 0L  = (0ᵢ Ad ) 
  
  evalB Ad (+L x1 x2 )  = ((+ Ad ) (evalB Ad x1 ) (evalB Ad x2 ) )
  
  evalCl : ({A  : Set }  → ((AdditiveMonoid A ) → ((ClAdditiveMonoidTerm A ) → A )))
  evalCl Ad (sing x1 )  = x1 
  
  evalCl Ad 0Cl  = (0ᵢ Ad ) 
  
  evalCl Ad (+Cl x1 x2 )  = ((+ Ad ) (evalCl Ad x1 ) (evalCl Ad x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AdditiveMonoid A ) → ((Vec A n ) → ((OpAdditiveMonoidTerm n ) → A ))))
  evalOp n Ad vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ad vars 0OL  = (0ᵢ Ad ) 
  
  evalOp n Ad vars (+OL x1 x2 )  = ((+ Ad ) (evalOp n Ad vars x1 ) (evalOp n Ad vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AdditiveMonoid A ) → ((Vec A n ) → ((OpAdditiveMonoidTerm2 n A ) → A ))))
  evalOpE n Ad vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ad vars (sing2 x1 )  = x1 
  
  evalOpE n Ad vars 0OL2  = (0ᵢ Ad ) 
  
  evalOpE n Ad vars (+OL2 x1 x2 )  = ((+ Ad ) (evalOpE n Ad vars x1 ) (evalOpE n Ad vars x2 ) )
  
  inductionB : ((P  : (AdditiveMonoidTerm  → Set ))  → ((P 0L ) → (((x1 x2  : AdditiveMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : AdditiveMonoidTerm )  → (P x )))))
  inductionB p p0l p+l 0L  = p0l 
  
  inductionB p p0l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p0l p+l x1 ) (inductionB p p0l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAdditiveMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClAdditiveMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClAdditiveMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing p0cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl p+cl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p0cl p+cl x1 ) (inductionCl _ p psing p0cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAdditiveMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpAdditiveMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpAdditiveMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv p0ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol p+ol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p0ol p+ol x1 ) (inductionOp _ p pv p0ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAdditiveMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpAdditiveMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpAdditiveMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 x2 ) )
  
  0L' : (  AdditiveMonoidTerm  )
  0L'  = 0L 
  
  +L' : (  (AdditiveMonoidTerm   → (AdditiveMonoidTerm   → AdditiveMonoidTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (AdditiveMonoidTerm  → (Staged AdditiveMonoidTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClAdditiveMonoidTerm A ) )
  0Cl'  = 0Cl 
  
  +Cl' : ({A  : Set }  → ((ClAdditiveMonoidTerm A )  → ((ClAdditiveMonoidTerm A )  → (ClAdditiveMonoidTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAdditiveMonoidTerm A ) → (Staged (ClAdditiveMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpAdditiveMonoidTerm n ) )
  0OL'  = 0OL 
  
  +OL' : ({n  : Nat}  → ((OpAdditiveMonoidTerm n )  → ((OpAdditiveMonoidTerm n )  → (OpAdditiveMonoidTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAdditiveMonoidTerm n ) → (Staged (OpAdditiveMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpAdditiveMonoidTerm2 n A ) )
  0OL2'  = 0OL2 
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveMonoidTerm2 n A )  → ((OpAdditiveMonoidTerm2 n A )  → (OpAdditiveMonoidTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveMonoidTerm2 n A ) → (Staged (OpAdditiveMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
