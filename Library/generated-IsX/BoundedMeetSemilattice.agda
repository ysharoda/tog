
 module BoundedMeetSemilattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsBoundedMeetSemilattice (A  : Set ) (*  : (A  → (A  → A ))) (1ᵢ  : A )  : Set where
    constructor IsBoundedMeetSemilatticeC
    field
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      idempotent_* : ({x  : A }  → (* x x ) ≡ x ) 
  
  record BoundedMeetSemilattice (A  : Set )  : Set where
    constructor BoundedMeetSemilatticeC
    field
      * : (A  → (A  → A ))
      1ᵢ : A 
      isBoundedMeetSemilattice : (IsBoundedMeetSemilattice A (*) 1ᵢ ) 
  
  open BoundedMeetSemilattice
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      1S : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      idempotent_*P : ({xP  : (Prod AP AP )}  → (*P xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Bo1  : (BoundedMeetSemilattice A1 )) (Bo2  : (BoundedMeetSemilattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Bo1 ) x1 x2 ) ) ≡ ((* Bo2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Bo1 )  ) ≡ (1ᵢ Bo2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Bo1  : (BoundedMeetSemilattice A1 )) (Bo2  : (BoundedMeetSemilattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Bo1 ) x1 x2 ) ((* Bo2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Bo1 )  (1ᵢ Bo2 )  )) 
  
  data BoundedMeetSemilatticeTerm  : Set where
    *L : (BoundedMeetSemilatticeTerm   → (BoundedMeetSemilatticeTerm   → BoundedMeetSemilatticeTerm  ))
    1L : BoundedMeetSemilatticeTerm   
  
  data ClBoundedMeetSemilatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClBoundedMeetSemilatticeTerm A ) )
    *Cl : ((ClBoundedMeetSemilatticeTerm A )  → ((ClBoundedMeetSemilatticeTerm A )  → (ClBoundedMeetSemilatticeTerm A ) ))
    1Cl : (ClBoundedMeetSemilatticeTerm A )  
  
  data OpBoundedMeetSemilatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpBoundedMeetSemilatticeTerm n ) )
    *OL : ((OpBoundedMeetSemilatticeTerm n )  → ((OpBoundedMeetSemilatticeTerm n )  → (OpBoundedMeetSemilatticeTerm n ) ))
    1OL : (OpBoundedMeetSemilatticeTerm n )  
  
  data OpBoundedMeetSemilatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpBoundedMeetSemilatticeTerm2 n A ) )
    sing2 : (A  → (OpBoundedMeetSemilatticeTerm2 n A ) )
    *OL2 : ((OpBoundedMeetSemilatticeTerm2 n A )  → ((OpBoundedMeetSemilatticeTerm2 n A )  → (OpBoundedMeetSemilatticeTerm2 n A ) ))
    1OL2 : (OpBoundedMeetSemilatticeTerm2 n A )  
  
  simplifyB : (BoundedMeetSemilatticeTerm  → BoundedMeetSemilatticeTerm )
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyCl : ((A  : Set )  → ((ClBoundedMeetSemilatticeTerm A ) → (ClBoundedMeetSemilatticeTerm A )))
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpBoundedMeetSemilatticeTerm n ) → (OpBoundedMeetSemilatticeTerm n )))
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedMeetSemilatticeTerm2 n A ) → (OpBoundedMeetSemilatticeTerm2 n A )))
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((BoundedMeetSemilattice A ) → (BoundedMeetSemilatticeTerm  → A )))
  evalB Bo (*L x1 x2 )  = ((* Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalB Bo 1L  = (1ᵢ Bo ) 
  
  evalCl : ({A  : Set }  → ((BoundedMeetSemilattice A ) → ((ClBoundedMeetSemilatticeTerm A ) → A )))
  evalCl Bo (sing x1 )  = x1 
  
  evalCl Bo (*Cl x1 x2 )  = ((* Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalCl Bo 1Cl  = (1ᵢ Bo ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((BoundedMeetSemilattice A ) → ((Vec A n ) → ((OpBoundedMeetSemilatticeTerm n ) → A ))))
  evalOp n Bo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Bo vars (*OL x1 x2 )  = ((* Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOp n Bo vars 1OL  = (1ᵢ Bo ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((BoundedMeetSemilattice A ) → ((Vec A n ) → ((OpBoundedMeetSemilatticeTerm2 n A ) → A ))))
  evalOpE n Bo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Bo vars (sing2 x1 )  = x1 
  
  evalOpE n Bo vars (*OL2 x1 x2 )  = ((* Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  evalOpE n Bo vars 1OL2  = (1ᵢ Bo ) 
  
  inductionB : ((P  : (BoundedMeetSemilatticeTerm  → Set ))  → (((x1 x2  : BoundedMeetSemilatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P 1L ) → ((x  : BoundedMeetSemilatticeTerm )  → (P x )))))
  inductionB p p*l p1l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p1l x1 ) (inductionB p p*l p1l x2 ) )
  
  inductionB p p*l p1l 1L  = p1l 
  
  inductionCl : ((A  : Set ) (P  : ((ClBoundedMeetSemilatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClBoundedMeetSemilatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P 1Cl ) → ((x  : (ClBoundedMeetSemilatticeTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p1cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p1cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p1cl x1 ) (inductionCl _ p psing p*cl p1cl x2 ) )
  
  inductionCl _ p psing p*cl p1cl 1Cl  = p1cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpBoundedMeetSemilatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpBoundedMeetSemilatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P 1OL ) → ((x  : (OpBoundedMeetSemilatticeTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p1ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p1ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p1ol x1 ) (inductionOp _ p pv p*ol p1ol x2 ) )
  
  inductionOp _ p pv p*ol p1ol 1OL  = p1ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpBoundedMeetSemilatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpBoundedMeetSemilatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P 1OL2 ) → ((x  : (OpBoundedMeetSemilatticeTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 1OL2  = p1ol2 
  
  *L' : (  (BoundedMeetSemilatticeTerm   → (BoundedMeetSemilatticeTerm   → BoundedMeetSemilatticeTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  1L' : (  BoundedMeetSemilatticeTerm  )
  1L'  = 1L 
  
  stageB : (BoundedMeetSemilatticeTerm  → (Staged BoundedMeetSemilatticeTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  *Cl' : ({A  : Set }  → ((ClBoundedMeetSemilatticeTerm A )  → ((ClBoundedMeetSemilatticeTerm A )  → (ClBoundedMeetSemilatticeTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClBoundedMeetSemilatticeTerm A ) )
  1Cl'  = 1Cl 
  
  stageCl : ((A  : Set )  → ((ClBoundedMeetSemilatticeTerm A ) → (Staged (ClBoundedMeetSemilatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  *OL' : ({n  : Nat}  → ((OpBoundedMeetSemilatticeTerm n )  → ((OpBoundedMeetSemilatticeTerm n )  → (OpBoundedMeetSemilatticeTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpBoundedMeetSemilatticeTerm n ) )
  1OL'  = 1OL 
  
  stageOp : ((n  : Nat)  → ((OpBoundedMeetSemilatticeTerm n ) → (Staged (OpBoundedMeetSemilatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpBoundedMeetSemilatticeTerm2 n A )  → ((OpBoundedMeetSemilatticeTerm2 n A )  → (OpBoundedMeetSemilatticeTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpBoundedMeetSemilatticeTerm2 n A ) )
  1OL2'  = 1OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedMeetSemilatticeTerm2 n A ) → (Staged (OpBoundedMeetSemilatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A )  
   
