module AdditiveGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveGroup (A  : Set )  : Set where
    constructor AdditiveGroupC
    field
      + : (A  → (A  → A ))
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      neg : (A  → A )
      leftInverse_inv_op_0ᵢ : ({x  : A }  → (+ x (neg x ) ) ≡ 0ᵢ )
      rightInverse_inv_op_0ᵢ : ({x  : A }  → (+ (neg x ) x ) ≡ 0ᵢ )
  open AdditiveGroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      0S : AS 
      negS : (AS  → AS )
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      0P : (Prod AP AP )
      negP : ((Prod AP AP ) → (Prod AP AP ))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      leftInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P xP (negP xP ) ) ≡ 0P )
      rightInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P (negP xP ) xP ) ≡ 0P )
  record Hom (A1 A2  : Set ) (Ad1  : (AdditiveGroup A1 )) (Ad2  : (AdditiveGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ad1 ) x1 x2 ) ) ≡ ((+ Ad2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Ad1 )  ) ≡ (0ᵢ Ad2 ) )
      pres-neg : ({x1  : A1}  → (hom ((neg Ad1 ) x1 ) ) ≡ ((neg Ad2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (Ad1  : (AdditiveGroup A1 )) (Ad2  : (AdditiveGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ad1 ) x1 x2 ) ((+ Ad2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Ad1 )  (0ᵢ Ad2 )  ))
      interp-neg : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((neg Ad1 ) x1 ) ((neg Ad2 ) y1 ) )))
  data AdditiveGroupTerm  : Set where
    +L : (AdditiveGroupTerm   → (AdditiveGroupTerm   → AdditiveGroupTerm  ))
    0L : AdditiveGroupTerm  
    negL : (AdditiveGroupTerm   → AdditiveGroupTerm  )
  data ClAdditiveGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClAdditiveGroupTerm A ) )
    +Cl : ((ClAdditiveGroupTerm A )  → ((ClAdditiveGroupTerm A )  → (ClAdditiveGroupTerm A ) ))
    0Cl : (ClAdditiveGroupTerm A ) 
    negCl : ((ClAdditiveGroupTerm A )  → (ClAdditiveGroupTerm A ) )
  data OpAdditiveGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAdditiveGroupTerm n ) )
    +OL : ((OpAdditiveGroupTerm n )  → ((OpAdditiveGroupTerm n )  → (OpAdditiveGroupTerm n ) ))
    0OL : (OpAdditiveGroupTerm n ) 
    negOL : ((OpAdditiveGroupTerm n )  → (OpAdditiveGroupTerm n ) )
  data OpAdditiveGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAdditiveGroupTerm2 n A ) )
    sing2 : (A  → (OpAdditiveGroupTerm2 n A ) )
    +OL2 : ((OpAdditiveGroupTerm2 n A )  → ((OpAdditiveGroupTerm2 n A )  → (OpAdditiveGroupTerm2 n A ) ))
    0OL2 : (OpAdditiveGroupTerm2 n A ) 
    negOL2 : ((OpAdditiveGroupTerm2 n A )  → (OpAdditiveGroupTerm2 n A ) )
  evalB : ({A  : Set }  → ((AdditiveGroup A ) → (AdditiveGroupTerm  → A )))
  evalB Ad (+L x1 x2 )  = ((+ Ad ) (evalB Ad x1 ) (evalB Ad x2 ) )
  
  evalB Ad 0L  = (0ᵢ Ad ) 
  
  evalB Ad (negL x1 )  = ((neg Ad ) (evalB Ad x1 ) )
  
  evalCl : ({A  : Set }  → ((AdditiveGroup A ) → ((ClAdditiveGroupTerm A ) → A )))
  evalCl Ad (sing x1 )  = x1 
  
  evalCl Ad (+Cl x1 x2 )  = ((+ Ad ) (evalCl Ad x1 ) (evalCl Ad x2 ) )
  
  evalCl Ad 0Cl  = (0ᵢ Ad ) 
  
  evalCl Ad (negCl x1 )  = ((neg Ad ) (evalCl Ad x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AdditiveGroup A ) → ((Vec A n ) → ((OpAdditiveGroupTerm n ) → A ))))
  evalOp n Ad vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ad vars (+OL x1 x2 )  = ((+ Ad ) (evalOp n Ad vars x1 ) (evalOp n Ad vars x2 ) )
  
  evalOp n Ad vars 0OL  = (0ᵢ Ad ) 
  
  evalOp n Ad vars (negOL x1 )  = ((neg Ad ) (evalOp n Ad vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AdditiveGroup A ) → ((Vec A n ) → ((OpAdditiveGroupTerm2 n A ) → A ))))
  evalOpE n Ad vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ad vars (sing2 x1 )  = x1 
  
  evalOpE n Ad vars (+OL2 x1 x2 )  = ((+ Ad ) (evalOpE n Ad vars x1 ) (evalOpE n Ad vars x2 ) )
  
  evalOpE n Ad vars 0OL2  = (0ᵢ Ad ) 
  
  evalOpE n Ad vars (negOL2 x1 )  = ((neg Ad ) (evalOpE n Ad vars x1 ) )
  
  inductionB : ((P  : (AdditiveGroupTerm  → Set ))  → (((x1 x2  : AdditiveGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → (((x1  : AdditiveGroupTerm  )  → ((P x1 ) → (P (negL x1 ) ))) → ((x  : AdditiveGroupTerm )  → (P x ))))))
  inductionB p p+l p0l pnegl (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p0l pnegl x1 ) (inductionB p p+l p0l pnegl x2 ) )
  
  inductionB p p+l p0l pnegl 0L  = p0l 
  
  inductionB p p+l p0l pnegl (negL x1 )  = (pnegl _ (inductionB p p+l p0l pnegl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAdditiveGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAdditiveGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → (((x1  : (ClAdditiveGroupTerm A ) )  → ((P x1 ) → (P (negCl x1 ) ))) → ((x  : (ClAdditiveGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing p+cl p0cl pnegcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p0cl pnegcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl x1 ) (inductionCl _ p psing p+cl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p+cl p0cl pnegcl 0Cl  = p0cl 
  
  inductionCl _ p psing p+cl p0cl pnegcl (negCl x1 )  = (pnegcl _ (inductionCl _ p psing p+cl p0cl pnegcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAdditiveGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAdditiveGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → (((x1  : (OpAdditiveGroupTerm n ) )  → ((P x1 ) → (P (negOL x1 ) ))) → ((x  : (OpAdditiveGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv p+ol p0ol pnegol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p0ol pnegol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p0ol pnegol x1 ) (inductionOp _ p pv p+ol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p+ol p0ol pnegol 0OL  = p0ol 
  
  inductionOp _ p pv p+ol p0ol pnegol (negOL x1 )  = (pnegol _ (inductionOp _ p pv p+ol p0ol pnegol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAdditiveGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAdditiveGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → (((x1  : (OpAdditiveGroupTerm2 n A ) )  → ((P x1 ) → (P (negOL2 x1 ) ))) → ((x  : (OpAdditiveGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (negOL2 x1 )  = (pnegol2 _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x1 ) )
  
  +L' : (  (AdditiveGroupTerm   → (AdditiveGroupTerm   → AdditiveGroupTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  AdditiveGroupTerm  )
  0L'  = 0L 
  
  negL' : (  (AdditiveGroupTerm   → AdditiveGroupTerm  ))
  negL' x1  = (negL x1 )
  
  stageB : (AdditiveGroupTerm  → (Staged AdditiveGroupTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  stageB (negL x1 )  = (stage1 negL' (codeLift1 negL' ) (stageB  x1 ) )
  
  +Cl' : ({A  : Set }  → ((ClAdditiveGroupTerm A )  → ((ClAdditiveGroupTerm A )  → (ClAdditiveGroupTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClAdditiveGroupTerm A ) )
  0Cl'  = 0Cl 
  
  negCl' : ({A  : Set }  → ((ClAdditiveGroupTerm A )  → (ClAdditiveGroupTerm A ) ))
  negCl' x1  = (negCl x1 )
  
  stageCl : ((A  : Set )  → ((ClAdditiveGroupTerm A ) → (Staged (ClAdditiveGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (negCl x1 )  = (stage1 negCl' (codeLift1 negCl' ) ((stageCl _ ) x1 ) )
  
  +OL' : ({n  : Nat}  → ((OpAdditiveGroupTerm n )  → ((OpAdditiveGroupTerm n )  → (OpAdditiveGroupTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpAdditiveGroupTerm n ) )
  0OL'  = 0OL 
  
  negOL' : ({n  : Nat}  → ((OpAdditiveGroupTerm n )  → (OpAdditiveGroupTerm n ) ))
  negOL' x1  = (negOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpAdditiveGroupTerm n ) → (Staged (OpAdditiveGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (negOL x1 )  = (stage1 negOL' (codeLift1 negOL' ) ((stageOp _ ) x1 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveGroupTerm2 n A )  → ((OpAdditiveGroupTerm2 n A )  → (OpAdditiveGroupTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpAdditiveGroupTerm2 n A ) )
  0OL2'  = 0OL2 
  
  negOL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveGroupTerm2 n A )  → (OpAdditiveGroupTerm2 n A ) ))
  negOL2' x1  = (negOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveGroupTerm2 n A ) → (Staged (OpAdditiveGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (negOL2 x1 )  = (stage1 negOL2' (codeLift1 negOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A ) 
      negT : ((Repr A )  → (Repr A ) )