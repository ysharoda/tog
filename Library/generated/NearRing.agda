module NearRing  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record NearRing (A  : Set )  : Set where
    constructor NearRingC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      neg : (A  → A )
      leftInverse_inv_op_0ᵢ : ({x  : A }  → (+ x (neg x ) ) ≡ 0ᵢ )
      rightInverse_inv_op_0ᵢ : ({x  : A }  → (+ (neg x ) x ) ≡ 0ᵢ )
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
  open NearRing
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
      0S : AS 
      negS : (AS  → AS )
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      0P : (Prod AP AP )
      negP : ((Prod AP AP ) → (Prod AP AP ))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      leftInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P xP (negP xP ) ) ≡ 0P )
      rightInverse_inv_op_0P : ({xP  : (Prod AP AP )}  → (+P (negP xP ) xP ) ≡ 0P )
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
  record Hom (A1 A2  : Set ) (Ne1  : (NearRing A1 )) (Ne2  : (NearRing A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ne1 ) x1 x2 ) ) ≡ ((* Ne2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ne1 ) x1 x2 ) ) ≡ ((+ Ne2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Ne1 )  ) ≡ (0ᵢ Ne2 ) )
      pres-neg : ({x1  : A1}  → (hom ((neg Ne1 ) x1 ) ) ≡ ((neg Ne2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (Ne1  : (NearRing A1 )) (Ne2  : (NearRing A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ne1 ) x1 x2 ) ((* Ne2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ne1 ) x1 x2 ) ((+ Ne2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Ne1 )  (0ᵢ Ne2 )  ))
      interp-neg : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((neg Ne1 ) x1 ) ((neg Ne2 ) y1 ) )))
  data NearRingTerm  : Set where
    *L : (NearRingTerm   → (NearRingTerm   → NearRingTerm  ))
    +L : (NearRingTerm   → (NearRingTerm   → NearRingTerm  ))
    0L : NearRingTerm  
    negL : (NearRingTerm   → NearRingTerm  )
  data ClNearRingTerm (A  : Set )  : Set where
    sing : (A  → (ClNearRingTerm A ) )
    *Cl : ((ClNearRingTerm A )  → ((ClNearRingTerm A )  → (ClNearRingTerm A ) ))
    +Cl : ((ClNearRingTerm A )  → ((ClNearRingTerm A )  → (ClNearRingTerm A ) ))
    0Cl : (ClNearRingTerm A ) 
    negCl : ((ClNearRingTerm A )  → (ClNearRingTerm A ) )
  data OpNearRingTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpNearRingTerm n ) )
    *OL : ((OpNearRingTerm n )  → ((OpNearRingTerm n )  → (OpNearRingTerm n ) ))
    +OL : ((OpNearRingTerm n )  → ((OpNearRingTerm n )  → (OpNearRingTerm n ) ))
    0OL : (OpNearRingTerm n ) 
    negOL : ((OpNearRingTerm n )  → (OpNearRingTerm n ) )
  data OpNearRingTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpNearRingTerm2 n A ) )
    sing2 : (A  → (OpNearRingTerm2 n A ) )
    *OL2 : ((OpNearRingTerm2 n A )  → ((OpNearRingTerm2 n A )  → (OpNearRingTerm2 n A ) ))
    +OL2 : ((OpNearRingTerm2 n A )  → ((OpNearRingTerm2 n A )  → (OpNearRingTerm2 n A ) ))
    0OL2 : (OpNearRingTerm2 n A ) 
    negOL2 : ((OpNearRingTerm2 n A )  → (OpNearRingTerm2 n A ) )
  evalB : ({A  : Set }  → ((NearRing A ) → (NearRingTerm  → A )))
  evalB Ne (*L x1 x2 )  = ((* Ne ) (evalB Ne x1 ) (evalB Ne x2 ) )
  
  evalB Ne (+L x1 x2 )  = ((+ Ne ) (evalB Ne x1 ) (evalB Ne x2 ) )
  
  evalB Ne 0L  = (0ᵢ Ne ) 
  
  evalB Ne (negL x1 )  = ((neg Ne ) (evalB Ne x1 ) )
  
  evalCl : ({A  : Set }  → ((NearRing A ) → ((ClNearRingTerm A ) → A )))
  evalCl Ne (sing x1 )  = x1 
  
  evalCl Ne (*Cl x1 x2 )  = ((* Ne ) (evalCl Ne x1 ) (evalCl Ne x2 ) )
  
  evalCl Ne (+Cl x1 x2 )  = ((+ Ne ) (evalCl Ne x1 ) (evalCl Ne x2 ) )
  
  evalCl Ne 0Cl  = (0ᵢ Ne ) 
  
  evalCl Ne (negCl x1 )  = ((neg Ne ) (evalCl Ne x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((NearRing A ) → ((Vec A n ) → ((OpNearRingTerm n ) → A ))))
  evalOp n Ne vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ne vars (*OL x1 x2 )  = ((* Ne ) (evalOp n Ne vars x1 ) (evalOp n Ne vars x2 ) )
  
  evalOp n Ne vars (+OL x1 x2 )  = ((+ Ne ) (evalOp n Ne vars x1 ) (evalOp n Ne vars x2 ) )
  
  evalOp n Ne vars 0OL  = (0ᵢ Ne ) 
  
  evalOp n Ne vars (negOL x1 )  = ((neg Ne ) (evalOp n Ne vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((NearRing A ) → ((Vec A n ) → ((OpNearRingTerm2 n A ) → A ))))
  evalOpE n Ne vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ne vars (sing2 x1 )  = x1 
  
  evalOpE n Ne vars (*OL2 x1 x2 )  = ((* Ne ) (evalOpE n Ne vars x1 ) (evalOpE n Ne vars x2 ) )
  
  evalOpE n Ne vars (+OL2 x1 x2 )  = ((+ Ne ) (evalOpE n Ne vars x1 ) (evalOpE n Ne vars x2 ) )
  
  evalOpE n Ne vars 0OL2  = (0ᵢ Ne ) 
  
  evalOpE n Ne vars (negOL2 x1 )  = ((neg Ne ) (evalOpE n Ne vars x1 ) )
  
  inductionB : ((P  : (NearRingTerm  → Set ))  → (((x1 x2  : NearRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : NearRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → (((x1  : NearRingTerm  )  → ((P x1 ) → (P (negL x1 ) ))) → ((x  : NearRingTerm )  → (P x )))))))
  inductionB p p*l p+l p0l pnegl (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l p0l pnegl x1 ) (inductionB p p*l p+l p0l pnegl x2 ) )
  
  inductionB p p*l p+l p0l pnegl (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l p0l pnegl x1 ) (inductionB p p*l p+l p0l pnegl x2 ) )
  
  inductionB p p*l p+l p0l pnegl 0L  = p0l 
  
  inductionB p p*l p+l p0l pnegl (negL x1 )  = (pnegl _ (inductionB p p*l p+l p0l pnegl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClNearRingTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClNearRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClNearRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → (((x1  : (ClNearRingTerm A ) )  → ((P x1 ) → (P (negCl x1 ) ))) → ((x  : (ClNearRingTerm A ))  → (P x ))))))))
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl p0cl pnegcl x1 ) (inductionCl _ p psing p*cl p+cl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl p0cl pnegcl x1 ) (inductionCl _ p psing p*cl p+cl p0cl pnegcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl 0Cl  = p0cl 
  
  inductionCl _ p psing p*cl p+cl p0cl pnegcl (negCl x1 )  = (pnegcl _ (inductionCl _ p psing p*cl p+cl p0cl pnegcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpNearRingTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpNearRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpNearRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → (((x1  : (OpNearRingTerm n ) )  → ((P x1 ) → (P (negOL x1 ) ))) → ((x  : (OpNearRingTerm n ))  → (P x ))))))))
  inductionOp _ p pv p*ol p+ol p0ol pnegol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol p0ol pnegol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol p0ol pnegol x1 ) (inductionOp _ p pv p*ol p+ol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p*ol p+ol p0ol pnegol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol p0ol pnegol x1 ) (inductionOp _ p pv p*ol p+ol p0ol pnegol x2 ) )
  
  inductionOp _ p pv p*ol p+ol p0ol pnegol 0OL  = p0ol 
  
  inductionOp _ p pv p*ol p+ol p0ol pnegol (negOL x1 )  = (pnegol _ (inductionOp _ p pv p*ol p+ol p0ol pnegol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpNearRingTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpNearRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpNearRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → (((x1  : (OpNearRingTerm2 n A ) )  → ((P x1 ) → (P (negOL2 x1 ) ))) → ((x  : (OpNearRingTerm2 n A ))  → (P x )))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 (negOL2 x1 )  = (pnegol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 x1 ) )
  
  *L' : (  (NearRingTerm   → (NearRingTerm   → NearRingTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (NearRingTerm   → (NearRingTerm   → NearRingTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  NearRingTerm  )
  0L'  = 0L 
  
  negL' : (  (NearRingTerm   → NearRingTerm  ))
  negL' x1  = (negL x1 )
  
  stageB : (NearRingTerm  → (Staged NearRingTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  stageB (negL x1 )  = (stage1 negL' (codeLift1 negL' ) (stageB  x1 ) )
  
  *Cl' : ({A  : Set }  → ((ClNearRingTerm A )  → ((ClNearRingTerm A )  → (ClNearRingTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClNearRingTerm A )  → ((ClNearRingTerm A )  → (ClNearRingTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClNearRingTerm A ) )
  0Cl'  = 0Cl 
  
  negCl' : ({A  : Set }  → ((ClNearRingTerm A )  → (ClNearRingTerm A ) ))
  negCl' x1  = (negCl x1 )
  
  stageCl : ((A  : Set )  → ((ClNearRingTerm A ) → (Staged (ClNearRingTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (negCl x1 )  = (stage1 negCl' (codeLift1 negCl' ) ((stageCl _ ) x1 ) )
  
  *OL' : ({n  : Nat}  → ((OpNearRingTerm n )  → ((OpNearRingTerm n )  → (OpNearRingTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpNearRingTerm n )  → ((OpNearRingTerm n )  → (OpNearRingTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpNearRingTerm n ) )
  0OL'  = 0OL 
  
  negOL' : ({n  : Nat}  → ((OpNearRingTerm n )  → (OpNearRingTerm n ) ))
  negOL' x1  = (negOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpNearRingTerm n ) → (Staged (OpNearRingTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (negOL x1 )  = (stage1 negOL' (codeLift1 negOL' ) ((stageOp _ ) x1 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpNearRingTerm2 n A )  → ((OpNearRingTerm2 n A )  → (OpNearRingTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpNearRingTerm2 n A )  → ((OpNearRingTerm2 n A )  → (OpNearRingTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpNearRingTerm2 n A ) )
  0OL2'  = 0OL2 
  
  negOL2' : ({n  : Nat } {A  : Set }  → ((OpNearRingTerm2 n A )  → (OpNearRingTerm2 n A ) ))
  negOL2' x1  = (negOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpNearRingTerm2 n A ) → (Staged (OpNearRingTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (negOL2 x1 )  = (stage1 negOL2' (codeLift1 negOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A ) 
      negT : ((Repr A )  → (Repr A ) )