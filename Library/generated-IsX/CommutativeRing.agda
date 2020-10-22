
 module CommutativeRing  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCommutativeRing (A  : Set ) (1ᵢ  : A ) (*  : (A  → (A  → A ))) (+  : (A  → (A  → A ))) (0ᵢ  : A ) (neg  : (A  → A ))  : Set where
    constructor IsCommutativeRingC
    field
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
      leftInverse_inv_op_0ᵢ : ({x  : A }  → (+ x (neg x ) ) ≡ 0ᵢ )
      rightInverse_inv_op_0ᵢ : ({x  : A }  → (+ (neg x ) x ) ≡ 0ᵢ )
      leftZero_op_0ᵢ : ({x  : A }  → (* 0ᵢ x ) ≡ 0ᵢ )
      rightZero_op_0ᵢ : ({x  : A }  → (* x 0ᵢ ) ≡ 0ᵢ ) 
  
  record CommutativeRing (A  : Set )  : Set where
    constructor CommutativeRingC
    field
      1ᵢ : A 
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      0ᵢ : A 
      neg : (A  → A )
      isCommutativeRing : (IsCommutativeRing A 1ᵢ (*) (+) 0ᵢ neg ) 
  
  open CommutativeRing
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      1S : AS 
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
      0S : AS 
      negS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      1P : (Prod AP AP )
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      0P : (Prod AP AP )
      negP : ((Prod AP AP ) → (Prod AP AP ))
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
      leftInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P xP (negP xP ) ) ≡ 0P )
      rightInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P (negP xP ) xP ) ≡ 0P )
      leftZero_op_0P : ({xP  : (Prod AP AP )}  → (*P 0P xP ) ≡ 0P )
      rightZero_op_0P : ({xP  : (Prod AP AP )}  → (*P xP 0P ) ≡ 0P ) 
  
  record Hom (A1 A2  : Set ) (Co1  : (CommutativeRing A1 )) (Co2  : (CommutativeRing A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-1 : (  (hom (1ᵢ Co1 )  ) ≡ (1ᵢ Co2 ) )
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Co1 ) x1 x2 ) ) ≡ ((* Co2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Co1 ) x1 x2 ) ) ≡ ((+ Co2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Co1 )  ) ≡ (0ᵢ Co2 ) )
      pres-neg : ({x1  : A1}  → (hom ((neg Co1 ) x1 ) ) ≡ ((neg Co2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Co1  : (CommutativeRing A1 )) (Co2  : (CommutativeRing A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-1 : (  (interp (1ᵢ Co1 )  (1ᵢ Co2 )  ))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Co1 ) x1 x2 ) ((* Co2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Co1 ) x1 x2 ) ((+ Co2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Co1 )  (0ᵢ Co2 )  ))
      interp-neg : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((neg Co1 ) x1 ) ((neg Co2 ) y1 ) ))) 
  
  data CommutativeRingTerm  : Set where
    1L : CommutativeRingTerm  
    *L : (CommutativeRingTerm   → (CommutativeRingTerm   → CommutativeRingTerm  ))
    +L : (CommutativeRingTerm   → (CommutativeRingTerm   → CommutativeRingTerm  ))
    0L : CommutativeRingTerm  
    negL : (CommutativeRingTerm   → CommutativeRingTerm  ) 
  
  data ClCommutativeRingTerm (A  : Set )  : Set where
    sing : (A  → (ClCommutativeRingTerm A ) )
    1Cl : (ClCommutativeRingTerm A ) 
    *Cl : ((ClCommutativeRingTerm A )  → ((ClCommutativeRingTerm A )  → (ClCommutativeRingTerm A ) ))
    +Cl : ((ClCommutativeRingTerm A )  → ((ClCommutativeRingTerm A )  → (ClCommutativeRingTerm A ) ))
    0Cl : (ClCommutativeRingTerm A ) 
    negCl : ((ClCommutativeRingTerm A )  → (ClCommutativeRingTerm A ) ) 
  
  data OpCommutativeRingTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCommutativeRingTerm n ) )
    1OL : (OpCommutativeRingTerm n ) 
    *OL : ((OpCommutativeRingTerm n )  → ((OpCommutativeRingTerm n )  → (OpCommutativeRingTerm n ) ))
    +OL : ((OpCommutativeRingTerm n )  → ((OpCommutativeRingTerm n )  → (OpCommutativeRingTerm n ) ))
    0OL : (OpCommutativeRingTerm n ) 
    negOL : ((OpCommutativeRingTerm n )  → (OpCommutativeRingTerm n ) ) 
  
  data OpCommutativeRingTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCommutativeRingTerm2 n A ) )
    sing2 : (A  → (OpCommutativeRingTerm2 n A ) )
    1OL2 : (OpCommutativeRingTerm2 n A ) 
    *OL2 : ((OpCommutativeRingTerm2 n A )  → ((OpCommutativeRingTerm2 n A )  → (OpCommutativeRingTerm2 n A ) ))
    +OL2 : ((OpCommutativeRingTerm2 n A )  → ((OpCommutativeRingTerm2 n A )  → (OpCommutativeRingTerm2 n A ) ))
    0OL2 : (OpCommutativeRingTerm2 n A ) 
    negOL2 : ((OpCommutativeRingTerm2 n A )  → (OpCommutativeRingTerm2 n A ) ) 
  
  simplifyB : (CommutativeRingTerm  → CommutativeRingTerm )
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB (+L 0L x )  = x 
  
  simplifyB (+L x 0L )  = x 
  
  simplifyB 1L  = 1L 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 0L  = 0L 
  
  simplifyB (negL x1 )  = (negL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClCommutativeRingTerm A ) → (ClCommutativeRingTerm A )))
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ (+Cl 0Cl x )  = x 
  
  simplifyCl _ (+Cl x 0Cl )  = x 
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (negCl x1 )  = (negCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpCommutativeRingTerm n ) → (OpCommutativeRingTerm n )))
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ (+OL 0OL x )  = x 
  
  simplifyOp _ (+OL x 0OL )  = x 
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (negOL x1 )  = (negOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeRingTerm2 n A ) → (OpCommutativeRingTerm2 n A )))
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ (+OL2 0OL2 x )  = x 
  
  simplifyOpE _ _ (+OL2 x 0OL2 )  = x 
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (negOL2 x1 )  = (negOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((CommutativeRing A ) → (CommutativeRingTerm  → A )))
  evalB Co 1L  = (1ᵢ Co ) 
  
  evalB Co (*L x1 x2 )  = ((* Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalB Co (+L x1 x2 )  = ((+ Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalB Co 0L  = (0ᵢ Co ) 
  
  evalB Co (negL x1 )  = ((neg Co ) (evalB Co x1 ) )
  
  evalCl : ({A  : Set }  → ((CommutativeRing A ) → ((ClCommutativeRingTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co 1Cl  = (1ᵢ Co ) 
  
  evalCl Co (*Cl x1 x2 )  = ((* Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalCl Co (+Cl x1 x2 )  = ((+ Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalCl Co 0Cl  = (0ᵢ Co ) 
  
  evalCl Co (negCl x1 )  = ((neg Co ) (evalCl Co x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CommutativeRing A ) → ((Vec A n ) → ((OpCommutativeRingTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars 1OL  = (1ᵢ Co ) 
  
  evalOp n Co vars (*OL x1 x2 )  = ((* Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOp n Co vars (+OL x1 x2 )  = ((+ Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOp n Co vars 0OL  = (0ᵢ Co ) 
  
  evalOp n Co vars (negOL x1 )  = ((neg Co ) (evalOp n Co vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CommutativeRing A ) → ((Vec A n ) → ((OpCommutativeRingTerm2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars 1OL2  = (1ᵢ Co ) 
  
  evalOpE n Co vars (*OL2 x1 x2 )  = ((* Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  evalOpE n Co vars (+OL2 x1 x2 )  = ((+ Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  evalOpE n Co vars 0OL2  = (0ᵢ Co ) 
  
  evalOpE n Co vars (negOL2 x1 )  = ((neg Co ) (evalOpE n Co vars x1 ) )
  
  inductionB : ((P  : (CommutativeRingTerm  → Set ))  → ((P 1L ) → (((x1 x2  : CommutativeRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : CommutativeRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → (((x1  : CommutativeRingTerm  )  → ((P x1 ) → (P (negL x1 ) ))) → ((x  : CommutativeRingTerm )  → (P x ))))))))
  inductionB p p1l p*l p+l p0l pnegl 1L  = p1l 
  
  inductionB p p1l p*l p+l p0l pnegl (*L x1 x2 )  = (p*l _ _ (inductionB p p1l p*l p+l p0l pnegl x1 ) (inductionB p p1l p*l p+l p0l pnegl x2 ) )
  
  inductionB p p1l p*l p+l p0l pnegl (+L x1 x2 )  = (p+l _ _ (inductionB p p1l p*l p+l p0l pnegl x1 ) (inductionB p p1l p*l p+l p0l pnegl x2 ) )
  
  inductionB p p1l p*l p+l p0l pnegl 0L  = p0l 
  
  inductionB p p1l p*l p+l p0l pnegl (negL x1 )  = (pnegl _ (inductionB p p1l p*l p+l p0l pnegl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClCommutativeRingTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 1Cl ) → (((x1 x2  : (ClCommutativeRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClCommutativeRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → (((x1  : (ClCommutativeRingTerm A ) )  → ((P x1 ) → (P (negCl x1 ) ))) → ((x  : (ClCommutativeRingTerm A ))  → (P x )))))))))
  inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl 1Cl  = p1cl 
  
  inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl x1 ) (inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl x1 ) (inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl 0Cl  = p0cl 
  
  inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl (negCl x1 )  = (pnegcl _ (inductionCl _ p psing p1cl p*cl p+cl p0cl pnegcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpCommutativeRingTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 1OL ) → (((x1 x2  : (OpCommutativeRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpCommutativeRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → (((x1  : (OpCommutativeRingTerm n ) )  → ((P x1 ) → (P (negOL x1 ) ))) → ((x  : (OpCommutativeRingTerm n ))  → (P x )))))))))
  inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol 1OL  = p1ol 
  
  inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol x1 ) (inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol x1 ) (inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol 0OL  = p0ol 
  
  inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol (negOL x1 )  = (pnegol _ (inductionOp _ p pv p1ol p*ol p+ol p0ol pnegol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCommutativeRingTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 1OL2 ) → (((x1 x2  : (OpCommutativeRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpCommutativeRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → (((x1  : (OpCommutativeRingTerm2 n A ) )  → ((P x1 ) → (P (negOL2 x1 ) ))) → ((x  : (OpCommutativeRingTerm2 n A ))  → (P x ))))))))))
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 (negOL2 x1 )  = (pnegol2 _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 p+ol2 p0ol2 pnegol2 x1 ) )
  
  1L' : (  CommutativeRingTerm  )
  1L'  = 1L 
  
  *L' : (  (CommutativeRingTerm   → (CommutativeRingTerm   → CommutativeRingTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (CommutativeRingTerm   → (CommutativeRingTerm   → CommutativeRingTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  CommutativeRingTerm  )
  0L'  = 0L 
  
  negL' : (  (CommutativeRingTerm   → CommutativeRingTerm  ))
  negL' x1  = (negL x1 )
  
  stageB : (CommutativeRingTerm  → (Staged CommutativeRingTerm  ))
  stageB 1L  = (Now 1L )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  stageB (negL x1 )  = (stage1 negL' (codeLift1 negL' ) (stageB  x1 ) )
  
  1Cl' : ({A  : Set }  → (ClCommutativeRingTerm A ) )
  1Cl'  = 1Cl 
  
  *Cl' : ({A  : Set }  → ((ClCommutativeRingTerm A )  → ((ClCommutativeRingTerm A )  → (ClCommutativeRingTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClCommutativeRingTerm A )  → ((ClCommutativeRingTerm A )  → (ClCommutativeRingTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClCommutativeRingTerm A ) )
  0Cl'  = 0Cl 
  
  negCl' : ({A  : Set }  → ((ClCommutativeRingTerm A )  → (ClCommutativeRingTerm A ) ))
  negCl' x1  = (negCl x1 )
  
  stageCl : ((A  : Set )  → ((ClCommutativeRingTerm A ) → (Staged (ClCommutativeRingTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (negCl x1 )  = (stage1 negCl' (codeLift1 negCl' ) ((stageCl _ ) x1 ) )
  
  1OL' : ({n  : Nat}  → (OpCommutativeRingTerm n ) )
  1OL'  = 1OL 
  
  *OL' : ({n  : Nat}  → ((OpCommutativeRingTerm n )  → ((OpCommutativeRingTerm n )  → (OpCommutativeRingTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpCommutativeRingTerm n )  → ((OpCommutativeRingTerm n )  → (OpCommutativeRingTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpCommutativeRingTerm n ) )
  0OL'  = 0OL 
  
  negOL' : ({n  : Nat}  → ((OpCommutativeRingTerm n )  → (OpCommutativeRingTerm n ) ))
  negOL' x1  = (negOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpCommutativeRingTerm n ) → (Staged (OpCommutativeRingTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (negOL x1 )  = (stage1 negOL' (codeLift1 negOL' ) ((stageOp _ ) x1 ) )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpCommutativeRingTerm2 n A ) )
  1OL2'  = 1OL2 
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeRingTerm2 n A )  → ((OpCommutativeRingTerm2 n A )  → (OpCommutativeRingTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeRingTerm2 n A )  → ((OpCommutativeRingTerm2 n A )  → (OpCommutativeRingTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpCommutativeRingTerm2 n A ) )
  0OL2'  = 0OL2 
  
  negOL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeRingTerm2 n A )  → (OpCommutativeRingTerm2 n A ) ))
  negOL2' x1  = (negOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeRingTerm2 n A ) → (Staged (OpCommutativeRingTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (negOL2 x1 )  = (stage1 negOL2' (codeLift1 negOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      1T : (Repr A ) 
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A ) 
      negT : ((Repr A )  → (Repr A ) ) 
   
