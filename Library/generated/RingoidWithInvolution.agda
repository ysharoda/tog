module RingoidWithInvolution  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RingoidWithInvolution (A  : Set )  : Set where
    constructor RingoidWithInvolutionC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
      prim : (A  → A )
  open RingoidWithInvolution
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
      primS : (AS  → AS )
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      primP : ((Prod AP AP ) → (Prod AP AP ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
  record Hom (A1 A2  : Set ) (Ri1  : (RingoidWithInvolution A1 )) (Ri2  : (RingoidWithInvolution A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ri1 ) x1 x2 ) ) ≡ ((* Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ri1 ) x1 x2 ) ) ≡ ((+ Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim Ri1 ) x1 ) ) ≡ ((prim Ri2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (Ri1  : (RingoidWithInvolution A1 )) (Ri2  : (RingoidWithInvolution A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ri1 ) x1 x2 ) ((* Ri2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ri1 ) x1 x2 ) ((+ Ri2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Ri1 ) x1 ) ((prim Ri2 ) y1 ) )))
  data RingoidWithInvolutionTerm  : Set where
    *L : (RingoidWithInvolutionTerm   → (RingoidWithInvolutionTerm   → RingoidWithInvolutionTerm  ))
    +L : (RingoidWithInvolutionTerm   → (RingoidWithInvolutionTerm   → RingoidWithInvolutionTerm  ))
    primL : (RingoidWithInvolutionTerm   → RingoidWithInvolutionTerm  )
  data ClRingoidWithInvolutionTerm (A  : Set )  : Set where
    sing : (A  → (ClRingoidWithInvolutionTerm A ) )
    *Cl : ((ClRingoidWithInvolutionTerm A )  → ((ClRingoidWithInvolutionTerm A )  → (ClRingoidWithInvolutionTerm A ) ))
    +Cl : ((ClRingoidWithInvolutionTerm A )  → ((ClRingoidWithInvolutionTerm A )  → (ClRingoidWithInvolutionTerm A ) ))
    primCl : ((ClRingoidWithInvolutionTerm A )  → (ClRingoidWithInvolutionTerm A ) )
  data OpRingoidWithInvolutionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRingoidWithInvolutionTerm n ) )
    *OL : ((OpRingoidWithInvolutionTerm n )  → ((OpRingoidWithInvolutionTerm n )  → (OpRingoidWithInvolutionTerm n ) ))
    +OL : ((OpRingoidWithInvolutionTerm n )  → ((OpRingoidWithInvolutionTerm n )  → (OpRingoidWithInvolutionTerm n ) ))
    primOL : ((OpRingoidWithInvolutionTerm n )  → (OpRingoidWithInvolutionTerm n ) )
  data OpRingoidWithInvolutionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRingoidWithInvolutionTerm2 n A ) )
    sing2 : (A  → (OpRingoidWithInvolutionTerm2 n A ) )
    *OL2 : ((OpRingoidWithInvolutionTerm2 n A )  → ((OpRingoidWithInvolutionTerm2 n A )  → (OpRingoidWithInvolutionTerm2 n A ) ))
    +OL2 : ((OpRingoidWithInvolutionTerm2 n A )  → ((OpRingoidWithInvolutionTerm2 n A )  → (OpRingoidWithInvolutionTerm2 n A ) ))
    primOL2 : ((OpRingoidWithInvolutionTerm2 n A )  → (OpRingoidWithInvolutionTerm2 n A ) )
  evalB : ({A  : Set }  → ((RingoidWithInvolution A ) → (RingoidWithInvolutionTerm  → A )))
  evalB Ri (*L x1 x2 )  = ((* Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (+L x1 x2 )  = ((+ Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (primL x1 )  = ((prim Ri ) (evalB Ri x1 ) )
  
  evalCl : ({A  : Set }  → ((RingoidWithInvolution A ) → ((ClRingoidWithInvolutionTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (*Cl x1 x2 )  = ((* Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (+Cl x1 x2 )  = ((+ Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (primCl x1 )  = ((prim Ri ) (evalCl Ri x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RingoidWithInvolution A ) → ((Vec A n ) → ((OpRingoidWithInvolutionTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (*OL x1 x2 )  = ((* Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (+OL x1 x2 )  = ((+ Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (primOL x1 )  = ((prim Ri ) (evalOp n Ri vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RingoidWithInvolution A ) → ((Vec A n ) → ((OpRingoidWithInvolutionTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (*OL2 x1 x2 )  = ((* Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (+OL2 x1 x2 )  = ((+ Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (primOL2 x1 )  = ((prim Ri ) (evalOpE n Ri vars x1 ) )
  
  inductionB : ((P  : (RingoidWithInvolutionTerm  → Set ))  → (((x1 x2  : RingoidWithInvolutionTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : RingoidWithInvolutionTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1  : RingoidWithInvolutionTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : RingoidWithInvolutionTerm )  → (P x ))))))
  inductionB p p*l p+l ppriml (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (primL x1 )  = (ppriml _ (inductionB p p*l p+l ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRingoidWithInvolutionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRingoidWithInvolutionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClRingoidWithInvolutionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1  : (ClRingoidWithInvolutionTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClRingoidWithInvolutionTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p+cl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl pprimcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRingoidWithInvolutionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRingoidWithInvolutionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpRingoidWithInvolutionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1  : (OpRingoidWithInvolutionTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpRingoidWithInvolutionTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p+ol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol pprimol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRingoidWithInvolutionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRingoidWithInvolutionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpRingoidWithInvolutionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1  : (OpRingoidWithInvolutionTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpRingoidWithInvolutionTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) )
  
  *L' : (  (RingoidWithInvolutionTerm   → (RingoidWithInvolutionTerm   → RingoidWithInvolutionTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (RingoidWithInvolutionTerm   → (RingoidWithInvolutionTerm   → RingoidWithInvolutionTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  primL' : (  (RingoidWithInvolutionTerm   → RingoidWithInvolutionTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (RingoidWithInvolutionTerm  → (Staged RingoidWithInvolutionTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  *Cl' : ({A  : Set }  → ((ClRingoidWithInvolutionTerm A )  → ((ClRingoidWithInvolutionTerm A )  → (ClRingoidWithInvolutionTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClRingoidWithInvolutionTerm A )  → ((ClRingoidWithInvolutionTerm A )  → (ClRingoidWithInvolutionTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClRingoidWithInvolutionTerm A )  → (ClRingoidWithInvolutionTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClRingoidWithInvolutionTerm A ) → (Staged (ClRingoidWithInvolutionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  *OL' : ({n  : Nat}  → ((OpRingoidWithInvolutionTerm n )  → ((OpRingoidWithInvolutionTerm n )  → (OpRingoidWithInvolutionTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpRingoidWithInvolutionTerm n )  → ((OpRingoidWithInvolutionTerm n )  → (OpRingoidWithInvolutionTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpRingoidWithInvolutionTerm n )  → (OpRingoidWithInvolutionTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpRingoidWithInvolutionTerm n ) → (Staged (OpRingoidWithInvolutionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoidWithInvolutionTerm2 n A )  → ((OpRingoidWithInvolutionTerm2 n A )  → (OpRingoidWithInvolutionTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoidWithInvolutionTerm2 n A )  → ((OpRingoidWithInvolutionTerm2 n A )  → (OpRingoidWithInvolutionTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpRingoidWithInvolutionTerm2 n A )  → (OpRingoidWithInvolutionTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoidWithInvolutionTerm2 n A ) → (Staged (OpRingoidWithInvolutionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      primT : ((Repr A )  → (Repr A ) )