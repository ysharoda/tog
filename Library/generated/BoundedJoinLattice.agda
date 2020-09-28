module BoundedJoinLattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BoundedJoinLattice (A  : Set )  : Set where
    constructor BoundedJoinLatticeC
    field
      + : (A  → (A  → A ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
      0ᵢ : A 
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      * : (A  → (A  → A ))
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      idempotent_* : ({x  : A }  → (* x x ) ≡ x )
      leftAbsorp_*_+ : ({x y  : A }  → (* x (+ x y ) ) ≡ x )
      leftAbsorp_+_* : ({x y  : A }  → (+ x (* x y ) ) ≡ x )
  open BoundedJoinLattice
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      0S : AS 
      *S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      0P : (Prod AP AP )
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP )
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      idempotent_*P : ({xP  : (Prod AP AP )}  → (*P xP xP ) ≡ xP )
      leftAbsorp_*_+P : ({xP yP  : (Prod AP AP )}  → (*P xP (+P xP yP ) ) ≡ xP )
      leftAbsorp_+_*P : ({xP yP  : (Prod AP AP )}  → (+P xP (*P xP yP ) ) ≡ xP )
  record Hom (A1 A2  : Set ) (Bo1  : (BoundedJoinLattice A1 )) (Bo2  : (BoundedJoinLattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Bo1 ) x1 x2 ) ) ≡ ((+ Bo2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Bo1 )  ) ≡ (0ᵢ Bo2 ) )
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Bo1 ) x1 x2 ) ) ≡ ((* Bo2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Bo1  : (BoundedJoinLattice A1 )) (Bo2  : (BoundedJoinLattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Bo1 ) x1 x2 ) ((+ Bo2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Bo1 )  (0ᵢ Bo2 )  ))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Bo1 ) x1 x2 ) ((* Bo2 ) y1 y2 ) ))))
  data BoundedJoinLatticeTerm  : Set where
    +L : (BoundedJoinLatticeTerm   → (BoundedJoinLatticeTerm   → BoundedJoinLatticeTerm  ))
    0L : BoundedJoinLatticeTerm  
    *L : (BoundedJoinLatticeTerm   → (BoundedJoinLatticeTerm   → BoundedJoinLatticeTerm  ))
  data ClBoundedJoinLatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClBoundedJoinLatticeTerm A ) )
    +Cl : ((ClBoundedJoinLatticeTerm A )  → ((ClBoundedJoinLatticeTerm A )  → (ClBoundedJoinLatticeTerm A ) ))
    0Cl : (ClBoundedJoinLatticeTerm A ) 
    *Cl : ((ClBoundedJoinLatticeTerm A )  → ((ClBoundedJoinLatticeTerm A )  → (ClBoundedJoinLatticeTerm A ) ))
  data OpBoundedJoinLatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpBoundedJoinLatticeTerm n ) )
    +OL : ((OpBoundedJoinLatticeTerm n )  → ((OpBoundedJoinLatticeTerm n )  → (OpBoundedJoinLatticeTerm n ) ))
    0OL : (OpBoundedJoinLatticeTerm n ) 
    *OL : ((OpBoundedJoinLatticeTerm n )  → ((OpBoundedJoinLatticeTerm n )  → (OpBoundedJoinLatticeTerm n ) ))
  data OpBoundedJoinLatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpBoundedJoinLatticeTerm2 n A ) )
    sing2 : (A  → (OpBoundedJoinLatticeTerm2 n A ) )
    +OL2 : ((OpBoundedJoinLatticeTerm2 n A )  → ((OpBoundedJoinLatticeTerm2 n A )  → (OpBoundedJoinLatticeTerm2 n A ) ))
    0OL2 : (OpBoundedJoinLatticeTerm2 n A ) 
    *OL2 : ((OpBoundedJoinLatticeTerm2 n A )  → ((OpBoundedJoinLatticeTerm2 n A )  → (OpBoundedJoinLatticeTerm2 n A ) ))
  evalB : ({A  : Set }  → ((BoundedJoinLattice A ) → (BoundedJoinLatticeTerm  → A )))
  evalB Bo (+L x1 x2 )  = ((+ Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalB Bo 0L  = (0ᵢ Bo ) 
  
  evalB Bo (*L x1 x2 )  = ((* Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalCl : ({A  : Set }  → ((BoundedJoinLattice A ) → ((ClBoundedJoinLatticeTerm A ) → A )))
  evalCl Bo (sing x1 )  = x1 
  
  evalCl Bo (+Cl x1 x2 )  = ((+ Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalCl Bo 0Cl  = (0ᵢ Bo ) 
  
  evalCl Bo (*Cl x1 x2 )  = ((* Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((BoundedJoinLattice A ) → ((Vec A n ) → ((OpBoundedJoinLatticeTerm n ) → A ))))
  evalOp n Bo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Bo vars (+OL x1 x2 )  = ((+ Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOp n Bo vars 0OL  = (0ᵢ Bo ) 
  
  evalOp n Bo vars (*OL x1 x2 )  = ((* Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((BoundedJoinLattice A ) → ((Vec A n ) → ((OpBoundedJoinLatticeTerm2 n A ) → A ))))
  evalOpE n Bo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Bo vars (sing2 x1 )  = x1 
  
  evalOpE n Bo vars (+OL2 x1 x2 )  = ((+ Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  evalOpE n Bo vars 0OL2  = (0ᵢ Bo ) 
  
  evalOpE n Bo vars (*OL2 x1 x2 )  = ((* Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  inductionB : ((P  : (BoundedJoinLatticeTerm  → Set ))  → (((x1 x2  : BoundedJoinLatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((P 0L ) → (((x1 x2  : BoundedJoinLatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : BoundedJoinLatticeTerm )  → (P x ))))))
  inductionB p p+l p0l p*l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p0l p*l x1 ) (inductionB p p+l p0l p*l x2 ) )
  
  inductionB p p+l p0l p*l 0L  = p0l 
  
  inductionB p p+l p0l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p+l p0l p*l x1 ) (inductionB p p+l p0l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClBoundedJoinLatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClBoundedJoinLatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((P 0Cl ) → (((x1 x2  : (ClBoundedJoinLatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClBoundedJoinLatticeTerm A ))  → (P x )))))))
  inductionCl _ p psing p+cl p0cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p0cl p*cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p0cl p*cl x1 ) (inductionCl _ p psing p+cl p0cl p*cl x2 ) )
  
  inductionCl _ p psing p+cl p0cl p*cl 0Cl  = p0cl 
  
  inductionCl _ p psing p+cl p0cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p+cl p0cl p*cl x1 ) (inductionCl _ p psing p+cl p0cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpBoundedJoinLatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpBoundedJoinLatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((P 0OL ) → (((x1 x2  : (OpBoundedJoinLatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpBoundedJoinLatticeTerm n ))  → (P x )))))))
  inductionOp _ p pv p+ol p0ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p0ol p*ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p0ol p*ol x1 ) (inductionOp _ p pv p+ol p0ol p*ol x2 ) )
  
  inductionOp _ p pv p+ol p0ol p*ol 0OL  = p0ol 
  
  inductionOp _ p pv p+ol p0ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p+ol p0ol p*ol x1 ) (inductionOp _ p pv p+ol p0ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpBoundedJoinLatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpBoundedJoinLatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((P 0OL2 ) → (((x1 x2  : (OpBoundedJoinLatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpBoundedJoinLatticeTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p0ol2 p*ol2 x2 ) )
  
  +L' : (  (BoundedJoinLatticeTerm   → (BoundedJoinLatticeTerm   → BoundedJoinLatticeTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  0L' : (  BoundedJoinLatticeTerm  )
  0L'  = 0L 
  
  *L' : (  (BoundedJoinLatticeTerm   → (BoundedJoinLatticeTerm   → BoundedJoinLatticeTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (BoundedJoinLatticeTerm  → (Staged BoundedJoinLatticeTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClBoundedJoinLatticeTerm A )  → ((ClBoundedJoinLatticeTerm A )  → (ClBoundedJoinLatticeTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClBoundedJoinLatticeTerm A ) )
  0Cl'  = 0Cl 
  
  *Cl' : ({A  : Set }  → ((ClBoundedJoinLatticeTerm A )  → ((ClBoundedJoinLatticeTerm A )  → (ClBoundedJoinLatticeTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClBoundedJoinLatticeTerm A ) → (Staged (ClBoundedJoinLatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpBoundedJoinLatticeTerm n )  → ((OpBoundedJoinLatticeTerm n )  → (OpBoundedJoinLatticeTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpBoundedJoinLatticeTerm n ) )
  0OL'  = 0OL 
  
  *OL' : ({n  : Nat}  → ((OpBoundedJoinLatticeTerm n )  → ((OpBoundedJoinLatticeTerm n )  → (OpBoundedJoinLatticeTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpBoundedJoinLatticeTerm n ) → (Staged (OpBoundedJoinLatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpBoundedJoinLatticeTerm2 n A )  → ((OpBoundedJoinLatticeTerm2 n A )  → (OpBoundedJoinLatticeTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpBoundedJoinLatticeTerm2 n A ) )
  0OL2'  = 0OL2 
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpBoundedJoinLatticeTerm2 n A )  → ((OpBoundedJoinLatticeTerm2 n A )  → (OpBoundedJoinLatticeTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpBoundedJoinLatticeTerm2 n A ) → (Staged (OpBoundedJoinLatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A ) 
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))