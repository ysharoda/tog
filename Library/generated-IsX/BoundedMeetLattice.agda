
 module BoundedMeetLattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsBoundedMeetLattice (A  : Set ) (*  : (A  → (A  → A ))) (1ᵢ  : A ) (+  : (A  → (A  → A )))  : Set where
    constructor IsBoundedMeetLatticeC
    field
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      idempotent_* : ({x  : A }  → (* x x ) ≡ x )
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
      leftAbsorp_*_+ : ({x y  : A }  → (* x (+ x y ) ) ≡ x )
      leftAbsorp_+_* : ({x y  : A }  → (+ x (* x y ) ) ≡ x ) 
  
  record BoundedMeetLattice (A  : Set )  : Set where
    constructor BoundedMeetLatticeC
    field
      * : (A  → (A  → A ))
      1ᵢ : A 
      + : (A  → (A  → A ))
      isBoundedMeetLattice : (IsBoundedMeetLattice A (*) 1ᵢ (+) ) 
  
  open BoundedMeetLattice
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      1S : AS 
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      idempotent_*P : ({xP  : (Prod AP AP )}  → (*P xP xP ) ≡ xP )
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP )
      leftAbsorp_*_+P : ({xP yP  : (Prod AP AP )}  → (*P xP (+P xP yP ) ) ≡ xP )
      leftAbsorp_+_*P : ({xP yP  : (Prod AP AP )}  → (+P xP (*P xP yP ) ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Bo1  : (BoundedMeetLattice A1 )) (Bo2  : (BoundedMeetLattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Bo1 ) x1 x2 ) ) ≡ ((* Bo2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Bo1 )  ) ≡ (1ᵢ Bo2 ) )
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Bo1 ) x1 x2 ) ) ≡ ((+ Bo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Bo1  : (BoundedMeetLattice A1 )) (Bo2  : (BoundedMeetLattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Bo1 ) x1 x2 ) ((* Bo2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Bo1 )  (1ᵢ Bo2 )  ))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Bo1 ) x1 x2 ) ((+ Bo2 ) y1 y2 ) )))) 
  
  data BoundedMeetLatticeTerm  : Set where
    *L : (BoundedMeetLatticeTerm   → (BoundedMeetLatticeTerm   → BoundedMeetLatticeTerm  ))
    1L : BoundedMeetLatticeTerm  
    +L : (BoundedMeetLatticeTerm   → (BoundedMeetLatticeTerm   → BoundedMeetLatticeTerm  )) 
  
  data ClBoundedMeetLatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClBoundedMeetLatticeTerm A ) )
    *Cl : ((ClBoundedMeetLatticeTerm A )  → ((ClBoundedMeetLatticeTerm A )  → (ClBoundedMeetLatticeTerm A ) ))
    1Cl : (ClBoundedMeetLatticeTerm A ) 
    +Cl : ((ClBoundedMeetLatticeTerm A )  → ((ClBoundedMeetLatticeTerm A )  → (ClBoundedMeetLatticeTerm A ) )) 
  
  data OpBoundedMeetLatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpBoundedMeetLatticeTerm n ) )
    *OL : ((OpBoundedMeetLatticeTerm n )  → ((OpBoundedMeetLatticeTerm n )  → (OpBoundedMeetLatticeTerm n ) ))
    1OL : (OpBoundedMeetLatticeTerm n ) 
    +OL : ((OpBoundedMeetLatticeTerm n )  → ((OpBoundedMeetLatticeTerm n )  → (OpBoundedMeetLatticeTerm n ) )) 
  
  data OpBoundedMeetLatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpBoundedMeetLatticeTerm2 n A ) )
    sing2 : (A  → (OpBoundedMeetLatticeTerm2 n A ) )
    *OL2 : ((OpBoundedMeetLatticeTerm2 n A )  → ((OpBoundedMeetLatticeTerm2 n A )  → (OpBoundedMeetLatticeTerm2 n A ) ))
    1OL2 : (OpBoundedMeetLatticeTerm2 n A ) 
    +OL2 : ((OpBoundedMeetLatticeTerm2 n A )  → ((OpBoundedMeetLatticeTerm2 n A )  → (OpBoundedMeetLatticeTerm2 n A ) )) 
  
  simplifyB : (BoundedMeetLatticeTerm  → BoundedMeetLatticeTerm )
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClBoundedMeetLatticeTerm A ) → (ClBoundedMeetLatticeTerm A )))
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpBoundedMeetLatticeTerm n ) → (OpBoundedMeetLatticeTerm n )))
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedMeetLatticeTerm2 n A ) → (OpBoundedMeetLatticeTerm2 n A )))
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((BoundedMeetLattice A ) → (BoundedMeetLatticeTerm  → A )))
  evalB Bo (*L x1 x2 )  = ((* Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalB Bo 1L  = (1ᵢ Bo ) 
  
  evalB Bo (+L x1 x2 )  = ((+ Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalCl : ({A  : Set }  → ((BoundedMeetLattice A ) → ((ClBoundedMeetLatticeTerm A ) → A )))
  evalCl Bo (sing x1 )  = x1 
  
  evalCl Bo (*Cl x1 x2 )  = ((* Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalCl Bo 1Cl  = (1ᵢ Bo ) 
  
  evalCl Bo (+Cl x1 x2 )  = ((+ Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((BoundedMeetLattice A ) → ((Vec A n ) → ((OpBoundedMeetLatticeTerm n ) → A ))))
  evalOp n Bo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Bo vars (*OL x1 x2 )  = ((* Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOp n Bo vars 1OL  = (1ᵢ Bo ) 
  
  evalOp n Bo vars (+OL x1 x2 )  = ((+ Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((BoundedMeetLattice A ) → ((Vec A n ) → ((OpBoundedMeetLatticeTerm2 n A ) → A ))))
  evalOpE n Bo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Bo vars (sing2 x1 )  = x1 
  
  evalOpE n Bo vars (*OL2 x1 x2 )  = ((* Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  evalOpE n Bo vars 1OL2  = (1ᵢ Bo ) 
  
  evalOpE n Bo vars (+OL2 x1 x2 )  = ((+ Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  inductionB : ((P  : (BoundedMeetLatticeTerm  → Set ))  → (((x1 x2  : BoundedMeetLatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P 1L ) → (((x1 x2  : BoundedMeetLatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : BoundedMeetLatticeTerm )  → (P x ))))))
  inductionB p p*l p1l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p1l p+l x1 ) (inductionB p p*l p1l p+l x2 ) )
  
  inductionB p p*l p1l p+l 1L  = p1l 
  
  inductionB p p*l p1l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p1l p+l x1 ) (inductionB p p*l p1l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClBoundedMeetLatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClBoundedMeetLatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P 1Cl ) → (((x1 x2  : (ClBoundedMeetLatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClBoundedMeetLatticeTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p1cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p1cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p1cl p+cl x1 ) (inductionCl _ p psing p*cl p1cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p1cl p+cl 1Cl  = p1cl 
  
  inductionCl _ p psing p*cl p1cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p1cl p+cl x1 ) (inductionCl _ p psing p*cl p1cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpBoundedMeetLatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpBoundedMeetLatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P 1OL ) → (((x1 x2  : (OpBoundedMeetLatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpBoundedMeetLatticeTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p1ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p1ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p1ol p+ol x1 ) (inductionOp _ p pv p*ol p1ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p1ol p+ol 1OL  = p1ol 
  
  inductionOp _ p pv p*ol p1ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p1ol p+ol x1 ) (inductionOp _ p pv p*ol p1ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpBoundedMeetLatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpBoundedMeetLatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P 1OL2 ) → (((x1 x2  : (OpBoundedMeetLatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpBoundedMeetLatticeTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 p+ol2 x2 ) )
  
  *L' : (  (BoundedMeetLatticeTerm   → (BoundedMeetLatticeTerm   → BoundedMeetLatticeTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  1L' : (  BoundedMeetLatticeTerm  )
  1L'  = 1L 
  
  +L' : (  (BoundedMeetLatticeTerm   → (BoundedMeetLatticeTerm   → BoundedMeetLatticeTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (BoundedMeetLatticeTerm  → (Staged BoundedMeetLatticeTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClBoundedMeetLatticeTerm A )  → ((ClBoundedMeetLatticeTerm A )  → (ClBoundedMeetLatticeTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClBoundedMeetLatticeTerm A ) )
  1Cl'  = 1Cl 
  
  +Cl' : ({A  : Set }  → ((ClBoundedMeetLatticeTerm A )  → ((ClBoundedMeetLatticeTerm A )  → (ClBoundedMeetLatticeTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClBoundedMeetLatticeTerm A ) → (Staged (ClBoundedMeetLatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpBoundedMeetLatticeTerm n )  → ((OpBoundedMeetLatticeTerm n )  → (OpBoundedMeetLatticeTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpBoundedMeetLatticeTerm n ) )
  1OL'  = 1OL 
  
  +OL' : ({n  : Nat}  → ((OpBoundedMeetLatticeTerm n )  → ((OpBoundedMeetLatticeTerm n )  → (OpBoundedMeetLatticeTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpBoundedMeetLatticeTerm n ) → (Staged (OpBoundedMeetLatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpBoundedMeetLatticeTerm2 n A )  → ((OpBoundedMeetLatticeTerm2 n A )  → (OpBoundedMeetLatticeTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpBoundedMeetLatticeTerm2 n A ) )
  1OL2'  = 1OL2 
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpBoundedMeetLatticeTerm2 n A )  → ((OpBoundedMeetLatticeTerm2 n A )  → (OpBoundedMeetLatticeTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedMeetLatticeTerm2 n A ) → (Staged (OpBoundedMeetLatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
