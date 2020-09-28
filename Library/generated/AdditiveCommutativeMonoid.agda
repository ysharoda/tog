module AdditiveCommutativeMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveCommutativeMonoid (A  : Set )  : Set where
    constructor AdditiveCommutativeMonoidC
    field
      + : (A  → (A  → A ))
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
  open AdditiveCommutativeMonoid
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      0S : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      0P : (Prod AP AP )
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
  record Hom (A1 A2  : Set ) (Ad1  : (AdditiveCommutativeMonoid A1 )) (Ad2  : (AdditiveCommutativeMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ad1 ) x1 x2 ) ) ≡ ((+ Ad2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Ad1 )  ) ≡ (0ᵢ Ad2 ) )
  record RelInterp (A1 A2  : Set ) (Ad1  : (AdditiveCommutativeMonoid A1 )) (Ad2  : (AdditiveCommutativeMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ad1 ) x1 x2 ) ((+ Ad2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Ad1 )  (0ᵢ Ad2 )  ))
  data AdditiveCommutativeMonoidTerm  : Set where
    +L : (AdditiveCommutativeMonoidTerm   → (AdditiveCommutativeMonoidTerm   → AdditiveCommutativeMonoidTerm  ))
    0L : AdditiveCommutativeMonoidTerm  
  data ClAdditiveCommutativeMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClAdditiveCommutativeMonoidTerm A ) )
    +Cl : ((ClAdditiveCommutativeMonoidTerm A )  → ((ClAdditiveCommutativeMonoidTerm A )  → (ClAdditiveCommutativeMonoidTerm A ) ))
    0Cl : (ClAdditiveCommutativeMonoidTerm A ) 
  data OpAdditiveCommutativeMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAdditiveCommutativeMonoidTerm n ) )
    +OL : ((OpAdditiveCommutativeMonoidTerm n )  → ((OpAdditiveCommutativeMonoidTerm n )  → (OpAdditiveCommutativeMonoidTerm n ) ))
    0OL : (OpAdditiveCommutativeMonoidTerm n ) 
  data OpAdditiveCommutativeMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAdditiveCommutativeMonoidTerm2 n A ) )
    sing2 : (A  → (OpAdditiveCommutativeMonoidTerm2 n A ) )
    +OL2 : ((OpAdditiveCommutativeMonoidTerm2 n A )  → ((OpAdditiveCommutativeMonoidTerm2 n A )  → (OpAdditiveCommutativeMonoidTerm2 n A ) ))
    0OL2 : (OpAdditiveCommutativeMonoidTerm2 n A ) 
  evalB : ({A  : Set }  → ((AdditiveCommutativeMonoid A ) → (AdditiveCommutativeMonoidTerm  → A )))
  evalB Ad (+L x1 x2 )  = ((+ Ad ) (evalB Ad x1 ) (evalB Ad x2 ) )
  
  evalB Ad 0L  = (0ᵢ Ad ) 
  
  evalCl : ({A  : Set }  → ((AdditiveCommutativeMonoid A ) → ((ClAdditiveCommutativeMonoidTerm A ) → A )))
  evalCl Ad (sing x1 )  = x1 
  
  evalCl Ad (+Cl x1 x2 )  = ((+ Ad ) (evalCl Ad x1 ) (evalCl Ad x2 ) )
  
  evalCl Ad 0Cl  = (0ᵢ Ad ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AdditiveCommutativeMonoid A ) → ((Vec A n ) → ((OpAdditiveCommutativeMonoidTerm n ) → A ))))
  evalOp n Ad vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ad vars (+OL x1 x2 )  = ((+ Ad ) (evalOp n Ad vars x1 ) (evalOp n Ad vars x2 ) )
  
  evalOp n Ad vars 0OL  = (0ᵢ Ad ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AdditiveCommutativeMonoid A ) → ((Vec A n ) → ((OpAdditiveCommutativeMonoidTerm2 n A ) → A ))))
  evalOpE n Ad vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ad vars (sing2 x1 )  = x1 
  
  evalOpE n Ad vars (+OL2 x1 x2 )  = ((+ Ad ) (evalOpE n Ad vars x1 ) (evalOpE n Ad vars x2 ) )
  
  evalOpE n Ad vars 0OL2  = (0ᵢ Ad ) 
  
  inductionB : ((P  : (AdditiveCommutativeMonoidTerm  → Set ))  → (((x1 x2  : AdditiveCommutativeMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → ((x  : AdditiveCommutativeMonoidTerm )  → (P x )))))
  inductionB p p+l p0l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p0l x1 ) (inductionB p p+l p0l x2 ) )
  
  inductionB p p+l p0l 0L  = p0l 
  
  inductionCl : ((A  : Set ) (P  : ((ClAdditiveCommutativeMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAdditiveCommutativeMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → ((x  : (ClAdditiveCommutativeMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing p+cl p0cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p0cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p0cl x1 ) (inductionCl _ p psing p+cl p0cl x2 ) )
  
  inductionCl _ p psing p+cl p0cl 0Cl  = p0cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpAdditiveCommutativeMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAdditiveCommutativeMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → ((x  : (OpAdditiveCommutativeMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv p+ol p0ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p0ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p0ol x1 ) (inductionOp _ p pv p+ol p0ol x2 ) )
  
  inductionOp _ p pv p+ol p0ol 0OL  = p0ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAdditiveCommutativeMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAdditiveCommutativeMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → ((x  : (OpAdditiveCommutativeMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 0OL2  = p0ol2 
  
  +L' : (  (AdditiveCommutativeMonoidTerm   → (AdditiveCommutativeMonoidTerm   → AdditiveCommutativeMonoidTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  AdditiveCommutativeMonoidTerm  )
  0L'  = 0L 
  
  stageB : (AdditiveCommutativeMonoidTerm  → (Staged AdditiveCommutativeMonoidTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  +Cl' : ({A  : Set }  → ((ClAdditiveCommutativeMonoidTerm A )  → ((ClAdditiveCommutativeMonoidTerm A )  → (ClAdditiveCommutativeMonoidTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClAdditiveCommutativeMonoidTerm A ) )
  0Cl'  = 0Cl 
  
  stageCl : ((A  : Set )  → ((ClAdditiveCommutativeMonoidTerm A ) → (Staged (ClAdditiveCommutativeMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  +OL' : ({n  : Nat}  → ((OpAdditiveCommutativeMonoidTerm n )  → ((OpAdditiveCommutativeMonoidTerm n )  → (OpAdditiveCommutativeMonoidTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpAdditiveCommutativeMonoidTerm n ) )
  0OL'  = 0OL 
  
  stageOp : ((n  : Nat)  → ((OpAdditiveCommutativeMonoidTerm n ) → (Staged (OpAdditiveCommutativeMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveCommutativeMonoidTerm2 n A )  → ((OpAdditiveCommutativeMonoidTerm2 n A )  → (OpAdditiveCommutativeMonoidTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpAdditiveCommutativeMonoidTerm2 n A ) )
  0OL2'  = 0OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveCommutativeMonoidTerm2 n A ) → (Staged (OpAdditiveCommutativeMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A ) 