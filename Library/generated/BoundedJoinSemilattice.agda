
 module BoundedJoinSemilattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BoundedJoinSemilattice (A  : Set )  : Set where
    constructor BoundedJoinSemilatticeC
    field
      + : (A  → (A  → A ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x ) 
  
  open BoundedJoinSemilattice
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
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Bo1  : (BoundedJoinSemilattice A1 )) (Bo2  : (BoundedJoinSemilattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Bo1 ) x1 x2 ) ) ≡ ((+ Bo2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Bo1 )  ) ≡ (0ᵢ Bo2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Bo1  : (BoundedJoinSemilattice A1 )) (Bo2  : (BoundedJoinSemilattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Bo1 ) x1 x2 ) ((+ Bo2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Bo1 )  (0ᵢ Bo2 )  )) 
  
  data BoundedJoinSemilatticeTerm  : Set where
    +L : (BoundedJoinSemilatticeTerm   → (BoundedJoinSemilatticeTerm   → BoundedJoinSemilatticeTerm  ))
    0L : BoundedJoinSemilatticeTerm   
  
  data ClBoundedJoinSemilatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClBoundedJoinSemilatticeTerm A ) )
    +Cl : ((ClBoundedJoinSemilatticeTerm A )  → ((ClBoundedJoinSemilatticeTerm A )  → (ClBoundedJoinSemilatticeTerm A ) ))
    0Cl : (ClBoundedJoinSemilatticeTerm A )  
  
  data OpBoundedJoinSemilatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpBoundedJoinSemilatticeTerm n ) )
    +OL : ((OpBoundedJoinSemilatticeTerm n )  → ((OpBoundedJoinSemilatticeTerm n )  → (OpBoundedJoinSemilatticeTerm n ) ))
    0OL : (OpBoundedJoinSemilatticeTerm n )  
  
  data OpBoundedJoinSemilatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpBoundedJoinSemilatticeTerm2 n A ) )
    sing2 : (A  → (OpBoundedJoinSemilatticeTerm2 n A ) )
    +OL2 : ((OpBoundedJoinSemilatticeTerm2 n A )  → ((OpBoundedJoinSemilatticeTerm2 n A )  → (OpBoundedJoinSemilatticeTerm2 n A ) ))
    0OL2 : (OpBoundedJoinSemilatticeTerm2 n A )  
  
  simplifyB : (BoundedJoinSemilatticeTerm  → BoundedJoinSemilatticeTerm )
  simplifyB (+L 0L x )  = x 
  
  simplifyB (+L x 0L )  = x 
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 0L  = 0L 
  
  simplifyCl : ((A  : Set )  → ((ClBoundedJoinSemilatticeTerm A ) → (ClBoundedJoinSemilatticeTerm A )))
  simplifyCl _ (+Cl 0Cl x )  = x 
  
  simplifyCl _ (+Cl x 0Cl )  = x 
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpBoundedJoinSemilatticeTerm n ) → (OpBoundedJoinSemilatticeTerm n )))
  simplifyOp _ (+OL 0OL x )  = x 
  
  simplifyOp _ (+OL x 0OL )  = x 
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedJoinSemilatticeTerm2 n A ) → (OpBoundedJoinSemilatticeTerm2 n A )))
  simplifyOpE _ _ (+OL2 0OL2 x )  = x 
  
  simplifyOpE _ _ (+OL2 x 0OL2 )  = x 
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((BoundedJoinSemilattice A ) → (BoundedJoinSemilatticeTerm  → A )))
  evalB Bo (+L x1 x2 )  = ((+ Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalB Bo 0L  = (0ᵢ Bo ) 
  
  evalCl : ({A  : Set }  → ((BoundedJoinSemilattice A ) → ((ClBoundedJoinSemilatticeTerm A ) → A )))
  evalCl Bo (sing x1 )  = x1 
  
  evalCl Bo (+Cl x1 x2 )  = ((+ Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalCl Bo 0Cl  = (0ᵢ Bo ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((BoundedJoinSemilattice A ) → ((Vec A n ) → ((OpBoundedJoinSemilatticeTerm n ) → A ))))
  evalOp n Bo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Bo vars (+OL x1 x2 )  = ((+ Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOp n Bo vars 0OL  = (0ᵢ Bo ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((BoundedJoinSemilattice A ) → ((Vec A n ) → ((OpBoundedJoinSemilatticeTerm2 n A ) → A ))))
  evalOpE n Bo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Bo vars (sing2 x1 )  = x1 
  
  evalOpE n Bo vars (+OL2 x1 x2 )  = ((+ Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  evalOpE n Bo vars 0OL2  = (0ᵢ Bo ) 
  
  inductionB : ((P  : (BoundedJoinSemilatticeTerm  → Set ))  → (((x1 x2  : BoundedJoinSemilatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → ((x  : BoundedJoinSemilatticeTerm )  → (P x )))))
  inductionB p p+l p0l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p0l x1 ) (inductionB p p+l p0l x2 ) )
  
  inductionB p p+l p0l 0L  = p0l 
  
  inductionCl : ((A  : Set ) (P  : ((ClBoundedJoinSemilatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClBoundedJoinSemilatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → ((x  : (ClBoundedJoinSemilatticeTerm A ))  → (P x ))))))
  inductionCl _ p psing p+cl p0cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p0cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p0cl x1 ) (inductionCl _ p psing p+cl p0cl x2 ) )
  
  inductionCl _ p psing p+cl p0cl 0Cl  = p0cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpBoundedJoinSemilatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpBoundedJoinSemilatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → ((x  : (OpBoundedJoinSemilatticeTerm n ))  → (P x ))))))
  inductionOp _ p pv p+ol p0ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p0ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p0ol x1 ) (inductionOp _ p pv p+ol p0ol x2 ) )
  
  inductionOp _ p pv p+ol p0ol 0OL  = p0ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpBoundedJoinSemilatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpBoundedJoinSemilatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → ((x  : (OpBoundedJoinSemilatticeTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 0OL2  = p0ol2 
  
  +L' : (  (BoundedJoinSemilatticeTerm   → (BoundedJoinSemilatticeTerm   → BoundedJoinSemilatticeTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  BoundedJoinSemilatticeTerm  )
  0L'  = 0L 
  
  stageB : (BoundedJoinSemilatticeTerm  → (Staged BoundedJoinSemilatticeTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  +Cl' : ({A  : Set }  → ((ClBoundedJoinSemilatticeTerm A )  → ((ClBoundedJoinSemilatticeTerm A )  → (ClBoundedJoinSemilatticeTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClBoundedJoinSemilatticeTerm A ) )
  0Cl'  = 0Cl 
  
  stageCl : ((A  : Set )  → ((ClBoundedJoinSemilatticeTerm A ) → (Staged (ClBoundedJoinSemilatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  +OL' : ({n  : Nat}  → ((OpBoundedJoinSemilatticeTerm n )  → ((OpBoundedJoinSemilatticeTerm n )  → (OpBoundedJoinSemilatticeTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpBoundedJoinSemilatticeTerm n ) )
  0OL'  = 0OL 
  
  stageOp : ((n  : Nat)  → ((OpBoundedJoinSemilatticeTerm n ) → (Staged (OpBoundedJoinSemilatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpBoundedJoinSemilatticeTerm2 n A )  → ((OpBoundedJoinSemilatticeTerm2 n A )  → (OpBoundedJoinSemilatticeTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpBoundedJoinSemilatticeTerm2 n A ) )
  0OL2'  = 0OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedJoinSemilatticeTerm2 n A ) → (Staged (OpBoundedJoinSemilatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A )  
   
