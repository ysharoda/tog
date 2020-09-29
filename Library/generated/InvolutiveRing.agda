
 module InvolutiveRing  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveRing (A  : Set )  : Set where
    constructor InvolutiveRingC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      1ᵢ : A 
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
      prim : (A  → A )
      fixes_prim_1ᵢ : (prim 1ᵢ ) ≡ 1ᵢ 
      involutive_prim : ({x  : A }  → (prim (prim x ) ) ≡ x )
      antidis_prim_+ : ({x y  : A }  → (prim (+ x y ) ) ≡ (+ (prim y ) (prim x ) ))
      antidis_prim_* : ({x y  : A }  → (prim (* x y ) ) ≡ (* (prim y ) (prim x ) ))
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      neg : (A  → A )
      leftInverse_inv_op_0ᵢ : ({x  : A }  → (+ x (neg x ) ) ≡ 0ᵢ )
      rightInverse_inv_op_0ᵢ : ({x  : A }  → (+ (neg x ) x ) ≡ 0ᵢ )
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      leftZero_op_0ᵢ : ({x  : A }  → (* 0ᵢ x ) ≡ 0ᵢ )
      rightZero_op_0ᵢ : ({x  : A }  → (* x 0ᵢ ) ≡ 0ᵢ ) 
  
  open InvolutiveRing
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
      1S : AS 
      primS : (AS  → AS )
      0S : AS 
      negS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      primP : ((Prod AP AP ) → (Prod AP AP ))
      0P : (Prod AP AP )
      negP : ((Prod AP AP ) → (Prod AP AP ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
      fixes_prim_1P : (primP 1P ) ≡ 1P 
      involutive_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ xP )
      antidis_prim_+P : ({xP yP  : (Prod AP AP )}  → (primP (+P xP yP ) ) ≡ (+P (primP yP ) (primP xP ) ))
      antidis_prim_*P : ({xP yP  : (Prod AP AP )}  → (primP (*P xP yP ) ) ≡ (*P (primP yP ) (primP xP ) ))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      leftInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P xP (negP xP ) ) ≡ 0P )
      rightInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P (negP xP ) xP ) ≡ 0P )
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      leftZero_op_0P : ({xP  : (Prod AP AP )}  → (*P 0P xP ) ≡ 0P )
      rightZero_op_0P : ({xP  : (Prod AP AP )}  → (*P xP 0P ) ≡ 0P ) 
  
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveRing A1 )) (In2  : (InvolutiveRing A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* In1 ) x1 x2 ) ) ≡ ((* In2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ In1 ) x1 x2 ) ) ≡ ((+ In2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ In1 )  ) ≡ (1ᵢ In2 ) )
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
      pres-0 : (  (hom (0ᵢ In1 )  ) ≡ (0ᵢ In2 ) )
      pres-neg : ({x1  : A1}  → (hom ((neg In1 ) x1 ) ) ≡ ((neg In2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveRing A1 )) (In2  : (InvolutiveRing A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* In1 ) x1 x2 ) ((* In2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ In1 ) x1 x2 ) ((+ In2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ In1 )  (1ᵢ In2 )  ))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
      interp-0 : (  (interp (0ᵢ In1 )  (0ᵢ In2 )  ))
      interp-neg : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((neg In1 ) x1 ) ((neg In2 ) y1 ) ))) 
  
  data InvolutiveRingTerm  : Set where
    *L : (InvolutiveRingTerm   → (InvolutiveRingTerm   → InvolutiveRingTerm  ))
    +L : (InvolutiveRingTerm   → (InvolutiveRingTerm   → InvolutiveRingTerm  ))
    1L : InvolutiveRingTerm  
    primL : (InvolutiveRingTerm   → InvolutiveRingTerm  )
    0L : InvolutiveRingTerm  
    negL : (InvolutiveRingTerm   → InvolutiveRingTerm  ) 
  
  data ClInvolutiveRingTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveRingTerm A ) )
    *Cl : ((ClInvolutiveRingTerm A )  → ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) ))
    +Cl : ((ClInvolutiveRingTerm A )  → ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) ))
    1Cl : (ClInvolutiveRingTerm A ) 
    primCl : ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) )
    0Cl : (ClInvolutiveRingTerm A ) 
    negCl : ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) ) 
  
  data OpInvolutiveRingTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveRingTerm n ) )
    *OL : ((OpInvolutiveRingTerm n )  → ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) ))
    +OL : ((OpInvolutiveRingTerm n )  → ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) ))
    1OL : (OpInvolutiveRingTerm n ) 
    primOL : ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) )
    0OL : (OpInvolutiveRingTerm n ) 
    negOL : ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) ) 
  
  data OpInvolutiveRingTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveRingTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveRingTerm2 n A ) )
    *OL2 : ((OpInvolutiveRingTerm2 n A )  → ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) ))
    +OL2 : ((OpInvolutiveRingTerm2 n A )  → ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) ))
    1OL2 : (OpInvolutiveRingTerm2 n A ) 
    primOL2 : ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) )
    0OL2 : (OpInvolutiveRingTerm2 n A ) 
    negOL2 : ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) ) 
  
  simplifyB : (InvolutiveRingTerm  → InvolutiveRingTerm )
  simplifyB (primL 1L )  = 1L 
  
  simplifyB (primL (primL x ) )  = x 
  
  simplifyB (+L (primL y ) (primL x ) )  = (primL (+L x y ) )
  
  simplifyB (*L (primL y ) (primL x ) )  = (primL (*L x y ) )
  
  simplifyB (+L 0L x )  = x 
  
  simplifyB (+L x 0L )  = x 
  
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB 0L  = 0L 
  
  simplifyB (negL x1 )  = (negL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInvolutiveRingTerm A ) → (ClInvolutiveRingTerm A )))
  simplifyCl _ (primCl 1Cl )  = 1Cl 
  
  simplifyCl _ (primCl (primCl x ) )  = x 
  
  simplifyCl _ (+Cl (primCl y ) (primCl x ) )  = (primCl (+Cl x y ) )
  
  simplifyCl _ (*Cl (primCl y ) (primCl x ) )  = (primCl (*Cl x y ) )
  
  simplifyCl _ (+Cl 0Cl x )  = x 
  
  simplifyCl _ (+Cl x 0Cl )  = x 
  
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (negCl x1 )  = (negCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutiveRingTerm n ) → (OpInvolutiveRingTerm n )))
  simplifyOp _ (primOL 1OL )  = 1OL 
  
  simplifyOp _ (primOL (primOL x ) )  = x 
  
  simplifyOp _ (+OL (primOL y ) (primOL x ) )  = (primOL (+OL x y ) )
  
  simplifyOp _ (*OL (primOL y ) (primOL x ) )  = (primOL (*OL x y ) )
  
  simplifyOp _ (+OL 0OL x )  = x 
  
  simplifyOp _ (+OL x 0OL )  = x 
  
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (negOL x1 )  = (negOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveRingTerm2 n A ) → (OpInvolutiveRingTerm2 n A )))
  simplifyOpE _ _ (primOL2 1OL2 )  = 1OL2 
  
  simplifyOpE _ _ (primOL2 (primOL2 x ) )  = x 
  
  simplifyOpE _ _ (+OL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (+OL2 x y ) )
  
  simplifyOpE _ _ (*OL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (*OL2 x y ) )
  
  simplifyOpE _ _ (+OL2 0OL2 x )  = x 
  
  simplifyOpE _ _ (+OL2 x 0OL2 )  = x 
  
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (negOL2 x1 )  = (negOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InvolutiveRing A ) → (InvolutiveRingTerm  → A )))
  evalB In (*L x1 x2 )  = ((* In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In (+L x1 x2 )  = ((+ In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In 1L  = (1ᵢ In ) 
  
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalB In 0L  = (0ᵢ In ) 
  
  evalB In (negL x1 )  = ((neg In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveRing A ) → ((ClInvolutiveRingTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (*Cl x1 x2 )  = ((* In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In (+Cl x1 x2 )  = ((+ In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In 1Cl  = (1ᵢ In ) 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalCl In 0Cl  = (0ᵢ In ) 
  
  evalCl In (negCl x1 )  = ((neg In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveRing A ) → ((Vec A n ) → ((OpInvolutiveRingTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (*OL x1 x2 )  = ((* In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars (+OL x1 x2 )  = ((+ In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars 1OL  = (1ᵢ In ) 
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars 0OL  = (0ᵢ In ) 
  
  evalOp n In vars (negOL x1 )  = ((neg In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveRing A ) → ((Vec A n ) → ((OpInvolutiveRingTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (*OL2 x1 x2 )  = ((* In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars (+OL2 x1 x2 )  = ((+ In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars 1OL2  = (1ᵢ In ) 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars 0OL2  = (0ᵢ In ) 
  
  evalOpE n In vars (negOL2 x1 )  = ((neg In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InvolutiveRingTerm  → Set ))  → (((x1 x2  : InvolutiveRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : InvolutiveRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 1L ) → (((x1  : InvolutiveRingTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((P 0L ) → (((x1  : InvolutiveRingTerm  )  → ((P x1 ) → (P (negL x1 ) ))) → ((x  : InvolutiveRingTerm )  → (P x )))))))))
  inductionB p p*l p+l p1l ppriml p0l pnegl (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l p1l ppriml p0l pnegl x1 ) (inductionB p p*l p+l p1l ppriml p0l pnegl x2 ) )
  
  inductionB p p*l p+l p1l ppriml p0l pnegl (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l p1l ppriml p0l pnegl x1 ) (inductionB p p*l p+l p1l ppriml p0l pnegl x2 ) )
  
  inductionB p p*l p+l p1l ppriml p0l pnegl 1L  = p1l 
  
  inductionB p p*l p+l p1l ppriml p0l pnegl (primL x1 )  = (ppriml _ (inductionB p p*l p+l p1l ppriml p0l pnegl x1 ) )
  
  inductionB p p*l p+l p1l ppriml p0l pnegl 0L  = p0l 
  
  inductionB p p*l p+l p1l ppriml p0l pnegl (negL x1 )  = (pnegl _ (inductionB p p*l p+l p1l ppriml p0l pnegl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveRingTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClInvolutiveRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClInvolutiveRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 1Cl ) → (((x1  : (ClInvolutiveRingTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((P 0Cl ) → (((x1  : (ClInvolutiveRingTerm A ) )  → ((P x1 ) → (P (negCl x1 ) ))) → ((x  : (ClInvolutiveRingTerm A ))  → (P x ))))))))))
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1 ) (inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1 ) (inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl 1Cl  = p1cl 
  
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1 ) )
  
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl 0Cl  = p0cl 
  
  inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl (negCl x1 )  = (pnegcl _ (inductionCl _ p psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveRingTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpInvolutiveRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpInvolutiveRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 1OL ) → (((x1  : (OpInvolutiveRingTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((P 0OL ) → (((x1  : (OpInvolutiveRingTerm n ) )  → ((P x1 ) → (P (negOL x1 ) ))) → ((x  : (OpInvolutiveRingTerm n ))  → (P x ))))))))))
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol x1 ) (inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol x1 ) (inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol 1OL  = p1ol 
  
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol x1 ) )
  
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol 0OL  = p0ol 
  
  inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol (negOL x1 )  = (pnegol _ (inductionOp _ p pv p*ol p+ol p1ol pprimol p0ol pnegol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveRingTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpInvolutiveRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpInvolutiveRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 1OL2 ) → (((x1  : (OpInvolutiveRingTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((P 0OL2 ) → (((x1  : (OpInvolutiveRingTerm2 n A ) )  → ((P x1 ) → (P (negOL2 x1 ) ))) → ((x  : (OpInvolutiveRingTerm2 n A ))  → (P x )))))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (negOL2 x1 )  = (pnegol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1 ) )
  
  *L' : (  (InvolutiveRingTerm   → (InvolutiveRingTerm   → InvolutiveRingTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (InvolutiveRingTerm   → (InvolutiveRingTerm   → InvolutiveRingTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  1L' : (  InvolutiveRingTerm  )
  1L'  = 1L 
  
  primL' : (  (InvolutiveRingTerm   → InvolutiveRingTerm  ))
  primL' x1  = (primL x1 )
  
  0L' : (  InvolutiveRingTerm  )
  0L'  = 0L 
  
  negL' : (  (InvolutiveRingTerm   → InvolutiveRingTerm  ))
  negL' x1  = (negL x1 )
  
  stageB : (InvolutiveRingTerm  → (Staged InvolutiveRingTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB 0L  = (Now 0L )
  
  stageB (negL x1 )  = (stage1 negL' (codeLift1 negL' ) (stageB  x1 ) )
  
  *Cl' : ({A  : Set }  → ((ClInvolutiveRingTerm A )  → ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClInvolutiveRingTerm A )  → ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClInvolutiveRingTerm A ) )
  1Cl'  = 1Cl 
  
  primCl' : ({A  : Set }  → ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  0Cl' : ({A  : Set }  → (ClInvolutiveRingTerm A ) )
  0Cl'  = 0Cl 
  
  negCl' : ({A  : Set }  → ((ClInvolutiveRingTerm A )  → (ClInvolutiveRingTerm A ) ))
  negCl' x1  = (negCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveRingTerm A ) → (Staged (ClInvolutiveRingTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (negCl x1 )  = (stage1 negCl' (codeLift1 negCl' ) ((stageCl _ ) x1 ) )
  
  *OL' : ({n  : Nat}  → ((OpInvolutiveRingTerm n )  → ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpInvolutiveRingTerm n )  → ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpInvolutiveRingTerm n ) )
  1OL'  = 1OL 
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  0OL' : ({n  : Nat}  → (OpInvolutiveRingTerm n ) )
  0OL'  = 0OL 
  
  negOL' : ({n  : Nat}  → ((OpInvolutiveRingTerm n )  → (OpInvolutiveRingTerm n ) ))
  negOL' x1  = (negOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveRingTerm n ) → (Staged (OpInvolutiveRingTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (negOL x1 )  = (stage1 negOL' (codeLift1 negOL' ) ((stageOp _ ) x1 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingTerm2 n A )  → ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingTerm2 n A )  → ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpInvolutiveRingTerm2 n A ) )
  1OL2'  = 1OL2 
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpInvolutiveRingTerm2 n A ) )
  0OL2'  = 0OL2 
  
  negOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingTerm2 n A )  → (OpInvolutiveRingTerm2 n A ) ))
  negOL2' x1  = (negOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveRingTerm2 n A ) → (Staged (OpInvolutiveRingTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (negOL2 x1 )  = (stage1 negOL2' (codeLift1 negOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 
      primT : ((Repr A )  → (Repr A ) )
      0T : (Repr A ) 
      negT : ((Repr A )  → (Repr A ) ) 
   
