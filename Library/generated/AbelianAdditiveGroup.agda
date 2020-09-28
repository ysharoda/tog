module AbelianAdditiveGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AbelianAdditiveGroup (A  : Set )  : Set where
    constructor AbelianAdditiveGroupC
    field
      + : (A  → (A  → A ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      neg : (A  → A )
      leftInverse_inv_op_0ᵢ : ({x  : A }  → (+ x (neg x ) ) ≡ 0ᵢ )
      rightInverse_inv_op_0ᵢ : ({x  : A }  → (+ (neg x ) x ) ≡ 0ᵢ )
  open AbelianAdditiveGroup
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
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      leftInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P xP (negP xP ) ) ≡ 0P )
      rightInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P (negP xP ) xP ) ≡ 0P )
  record Hom (A1 A2  : Set ) (Ab1  : (AbelianAdditiveGroup A1 )) (Ab2  : (AbelianAdditiveGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ab1 ) x1 x2 ) ) ≡ ((+ Ab2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Ab1 )  ) ≡ (0ᵢ Ab2 ) )
      pres-neg : ({x1  : A1}  → (hom ((neg Ab1 ) x1 ) ) ≡ ((neg Ab2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (Ab1  : (AbelianAdditiveGroup A1 )) (Ab2  : (AbelianAdditiveGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ab1 ) x1 x2 ) ((+ Ab2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Ab1 )  (0ᵢ Ab2 )  ))
      interp-neg : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((neg Ab1 ) x1 ) ((neg Ab2 ) y1 ) )))
  data AbelianAdditiveGroupTerm  : Set where
    +L : (AbelianAdditiveGroupTerm   → (AbelianAdditiveGroupTerm   → AbelianAdditiveGroupTerm  ))
    0L : AbelianAdditiveGroupTerm  
    negL : (AbelianAdditiveGroupTerm   → AbelianAdditiveGroupTerm  )
  data ClAbelianAdditiveGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClAbelianAdditiveGroupTerm A ) )
    +Cl : ((ClAbelianAdditiveGroupTerm A )  → ((ClAbelianAdditiveGroupTerm A )  → (ClAbelianAdditiveGroupTerm A ) ))
    0Cl : (ClAbelianAdditiveGroupTerm A ) 
    negCl : ((ClAbelianAdditiveGroupTerm A )  → (ClAbelianAdditiveGroupTerm A ) )
  data OpAbelianAdditiveGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAbelianAdditiveGroupTerm n ) )
    +OL : ((OpAbelianAdditiveGroupTerm n )  → ((OpAbelianAdditiveGroupTerm n )  → (OpAbelianAdditiveGroupTerm n ) ))
    0OL : (OpAbelianAdditiveGroupTerm n ) 
    negOL : ((OpAbelianAdditiveGroupTerm n )  → (OpAbelianAdditiveGroupTerm n ) )
  data OpAbelianAdditiveGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAbelianAdditiveGroupTerm2 n A ) )
    sing2 : (A  → (OpAbelianAdditiveGroupTerm2 n A ) )
    +OL2 : ((OpAbelianAdditiveGroupTerm2 n A )  → ((OpAbelianAdditiveGroupTerm2 n A )  → (OpAbelianAdditiveGroupTerm2 n A ) ))
    0OL2 : (OpAbelianAdditiveGroupTerm2 n A ) 
    negOL2 : ((OpAbelianAdditiveGroupTerm2 n A )  → (OpAbelianAdditiveGroupTerm2 n A ) )
  evalB : ({A  : Set }  → ((AbelianAdditiveGroup A ) → (AbelianAdditiveGroupTerm  → A )))
  evalB Ab (+L x1 x2 )  = ((+ Ab ) (evalB Ab x1 ) (evalB Ab x2 ) )
  
  evalB Ab 0L  = (0ᵢ Ab ) 
  
  evalB Ab (negL x1 )  = ((neg Ab ) (evalB Ab x1 ) )
  
  evalCl : ({A  : Set }  → ((AbelianAdditiveGroup A ) → ((ClAbelianAdditiveGroupTerm A ) → A )))
  evalCl Ab (sing x1 )  = x1 
  
  evalCl Ab (+Cl x1 x2 )  = ((+ Ab ) (evalCl Ab x1 ) (evalCl Ab x2 ) )
  
  evalCl Ab 0Cl  = (0ᵢ Ab ) 
  
  evalCl Ab (negCl x1 )  = ((neg Ab ) (evalCl Ab x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AbelianAdditiveGroup A ) → ((Vec A n ) → ((OpAbelianAdditiveGroupTerm n ) → A ))))
  evalOp n Ab vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ab vars (+OL x1 x2 )  = ((+ Ab ) (evalOp n Ab vars x1 ) (evalOp n Ab vars x2 ) )
  
  evalOp n Ab vars 0OL  = (0ᵢ Ab ) 
  
  evalOp n Ab vars (negOL x1 )  = ((neg Ab ) (evalOp n Ab vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AbelianAdditiveGroup A ) → ((Vec A n ) → ((OpAbelianAdditiveGroupTerm2 n A ) → A ))))
  evalOpE n Ab vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ab vars (sing2 x1 )  = x1 
  
  evalOpE n Ab vars (+OL2 x1 x2 )  = ((+ Ab ) (evalOpE n Ab vars x1 ) (evalOpE n Ab vars x2 ) )
  
  evalOpE n Ab vars 0OL2  = (0ᵢ Ab ) 
  
  evalOpE n Ab vars (negOL2 x1 )  = ((neg Ab ) (evalOpE n Ab vars x1 ) )
  
  inductionB : ((P  : (AbelianAdditiveGroupTerm  → Set ))  → (((x1 x2  : AbelianAdditiveGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → (((x1  : AbelianAdditiveGroupTerm  )  → ((P x1 ) → (P (negL x1 ) ))) → ((x  : AbelianAdditiveGroupTerm )  → (P x ))))))
  inductionB p p+l p0l pnegl (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p0l pnegl x1 ) (inductionB p p+l p0l pnegl x2 ) )
  
  inductionB p p+l p0l pnegl 0L  = p0l 
  
  inductionB p p+l p0l pnegl (negL x1 )  = (pnegl _ (inductionB p p+l p0l pnegl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAbelianAdditiveGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAbelianAdditiveGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → (((x1  : (ClAbelianAdditiveGroupTerm A ) )  → ((P x1 ) → (P (negCl x1 ) ))) → ((x  : (ClAbelianAdditiveGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing p+cl p0cl pnegcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p0cl pnegcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p0cl pnegcl x1 ) (inductionCl _ p psing p+cl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p+cl p0cl pnegcl 0Cl  = p0cl 
  
  inductionCl _ p psing p+cl p0cl pnegcl (negCl x1 )  = (pnegcl _ (inductionCl _ p psing p+cl p0cl pnegcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAbelianAdditiveGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAbelianAdditiveGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → (((x1  : (OpAbelianAdditiveGroupTerm n ) )  → ((P x1 ) → (P (negOL x1 ) ))) → ((x  : (OpAbelianAdditiveGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv p+ol p0ol pnegol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p0ol pnegol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p0ol pnegol x1 ) (inductionOp _ p pv p+ol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p+ol p0ol pnegol 0OL  = p0ol 
  
  inductionOp _ p pv p+ol p0ol pnegol (negOL x1 )  = (pnegol _ (inductionOp _ p pv p+ol p0ol pnegol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAbelianAdditiveGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAbelianAdditiveGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → (((x1  : (OpAbelianAdditiveGroupTerm2 n A ) )  → ((P x1 ) → (P (negOL2 x1 ) ))) → ((x  : (OpAbelianAdditiveGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 (negOL2 x1 )  = (pnegol2 _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 pnegol2 x1 ) )
  
  +L' : (  (AbelianAdditiveGroupTerm   → (AbelianAdditiveGroupTerm   → AbelianAdditiveGroupTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  AbelianAdditiveGroupTerm  )
  0L'  = 0L 
  
  negL' : (  (AbelianAdditiveGroupTerm   → AbelianAdditiveGroupTerm  ))
  negL' x1  = (negL x1 )
  
  stageB : (AbelianAdditiveGroupTerm  → (Staged AbelianAdditiveGroupTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  stageB (negL x1 )  = (stage1 negL' (codeLift1 negL' ) (stageB  x1 ) )
  
  +Cl' : ({A  : Set }  → ((ClAbelianAdditiveGroupTerm A )  → ((ClAbelianAdditiveGroupTerm A )  → (ClAbelianAdditiveGroupTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClAbelianAdditiveGroupTerm A ) )
  0Cl'  = 0Cl 
  
  negCl' : ({A  : Set }  → ((ClAbelianAdditiveGroupTerm A )  → (ClAbelianAdditiveGroupTerm A ) ))
  negCl' x1  = (negCl x1 )
  
  stageCl : ((A  : Set )  → ((ClAbelianAdditiveGroupTerm A ) → (Staged (ClAbelianAdditiveGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (negCl x1 )  = (stage1 negCl' (codeLift1 negCl' ) ((stageCl _ ) x1 ) )
  
  +OL' : ({n  : Nat}  → ((OpAbelianAdditiveGroupTerm n )  → ((OpAbelianAdditiveGroupTerm n )  → (OpAbelianAdditiveGroupTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpAbelianAdditiveGroupTerm n ) )
  0OL'  = 0OL 
  
  negOL' : ({n  : Nat}  → ((OpAbelianAdditiveGroupTerm n )  → (OpAbelianAdditiveGroupTerm n ) ))
  negOL' x1  = (negOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpAbelianAdditiveGroupTerm n ) → (Staged (OpAbelianAdditiveGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (negOL x1 )  = (stage1 negOL' (codeLift1 negOL' ) ((stageOp _ ) x1 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAbelianAdditiveGroupTerm2 n A )  → ((OpAbelianAdditiveGroupTerm2 n A )  → (OpAbelianAdditiveGroupTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpAbelianAdditiveGroupTerm2 n A ) )
  0OL2'  = 0OL2 
  
  negOL2' : ({n  : Nat } {A  : Set }  → ((OpAbelianAdditiveGroupTerm2 n A )  → (OpAbelianAdditiveGroupTerm2 n A ) ))
  negOL2' x1  = (negOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAbelianAdditiveGroupTerm2 n A ) → (Staged (OpAbelianAdditiveGroupTerm2 n A ) )))
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