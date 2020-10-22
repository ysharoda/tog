
 module IdempotentSemiRng  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsIdempotentSemiRng (A  : Set ) (+  : (A  → (A  → A ))) (*  : (A  → (A  → A ))) (0ᵢ  : A )  : Set where
    constructor IsIdempotentSemiRngC
    field
      lunit_0ᵢ : ({x  : A }  → (+ 0ᵢ x ) ≡ x )
      runit_0ᵢ : ({x  : A }  → (+ x 0ᵢ ) ≡ x )
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x ) 
  
  record IdempotentSemiRng (A  : Set )  : Set where
    constructor IdempotentSemiRngC
    field
      + : (A  → (A  → A ))
      * : (A  → (A  → A ))
      0ᵢ : A 
      isIdempotentSemiRng : (IsIdempotentSemiRng A (+) (*) 0ᵢ ) 
  
  open IdempotentSemiRng
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      *S : (AS  → (AS  → AS ))
      0S : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      0P : (Prod AP AP )
      lunit_0P : ({xP  : (Prod AP AP )}  → (+P 0P xP ) ≡ xP )
      runit_0P : ({xP  : (Prod AP AP )}  → (+P xP 0P ) ≡ xP )
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Id1  : (IdempotentSemiRng A1 )) (Id2  : (IdempotentSemiRng A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Id1 ) x1 x2 ) ) ≡ ((+ Id2 ) (hom x1 ) (hom x2 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Id1 ) x1 x2 ) ) ≡ ((* Id2 ) (hom x1 ) (hom x2 ) ))
      pres-0 : (  (hom (0ᵢ Id1 )  ) ≡ (0ᵢ Id2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Id1  : (IdempotentSemiRng A1 )) (Id2  : (IdempotentSemiRng A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Id1 ) x1 x2 ) ((+ Id2 ) y1 y2 ) ))))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Id1 ) x1 x2 ) ((* Id2 ) y1 y2 ) ))))
      interp-0 : (  (interp (0ᵢ Id1 )  (0ᵢ Id2 )  )) 
  
  data IdempotentSemiRngTerm  : Set where
    +L : (IdempotentSemiRngTerm   → (IdempotentSemiRngTerm   → IdempotentSemiRngTerm  ))
    *L : (IdempotentSemiRngTerm   → (IdempotentSemiRngTerm   → IdempotentSemiRngTerm  ))
    0L : IdempotentSemiRngTerm   
  
  data ClIdempotentSemiRngTerm (A  : Set )  : Set where
    sing : (A  → (ClIdempotentSemiRngTerm A ) )
    +Cl : ((ClIdempotentSemiRngTerm A )  → ((ClIdempotentSemiRngTerm A )  → (ClIdempotentSemiRngTerm A ) ))
    *Cl : ((ClIdempotentSemiRngTerm A )  → ((ClIdempotentSemiRngTerm A )  → (ClIdempotentSemiRngTerm A ) ))
    0Cl : (ClIdempotentSemiRngTerm A )  
  
  data OpIdempotentSemiRngTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpIdempotentSemiRngTerm n ) )
    +OL : ((OpIdempotentSemiRngTerm n )  → ((OpIdempotentSemiRngTerm n )  → (OpIdempotentSemiRngTerm n ) ))
    *OL : ((OpIdempotentSemiRngTerm n )  → ((OpIdempotentSemiRngTerm n )  → (OpIdempotentSemiRngTerm n ) ))
    0OL : (OpIdempotentSemiRngTerm n )  
  
  data OpIdempotentSemiRngTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpIdempotentSemiRngTerm2 n A ) )
    sing2 : (A  → (OpIdempotentSemiRngTerm2 n A ) )
    +OL2 : ((OpIdempotentSemiRngTerm2 n A )  → ((OpIdempotentSemiRngTerm2 n A )  → (OpIdempotentSemiRngTerm2 n A ) ))
    *OL2 : ((OpIdempotentSemiRngTerm2 n A )  → ((OpIdempotentSemiRngTerm2 n A )  → (OpIdempotentSemiRngTerm2 n A ) ))
    0OL2 : (OpIdempotentSemiRngTerm2 n A )  
  
  simplifyB : (IdempotentSemiRngTerm  → IdempotentSemiRngTerm )
  simplifyB (+L 0L x )  = x 
  
  simplifyB (+L x 0L )  = x 
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 0L  = 0L 
  
  simplifyCl : ((A  : Set )  → ((ClIdempotentSemiRngTerm A ) → (ClIdempotentSemiRngTerm A )))
  simplifyCl _ (+Cl 0Cl x )  = x 
  
  simplifyCl _ (+Cl x 0Cl )  = x 
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpIdempotentSemiRngTerm n ) → (OpIdempotentSemiRngTerm n )))
  simplifyOp _ (+OL 0OL x )  = x 
  
  simplifyOp _ (+OL x 0OL )  = x 
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentSemiRngTerm2 n A ) → (OpIdempotentSemiRngTerm2 n A )))
  simplifyOpE _ _ (+OL2 0OL2 x )  = x 
  
  simplifyOpE _ _ (+OL2 x 0OL2 )  = x 
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((IdempotentSemiRng A ) → (IdempotentSemiRngTerm  → A )))
  evalB Id (+L x1 x2 )  = ((+ Id ) (evalB Id x1 ) (evalB Id x2 ) )
  
  evalB Id (*L x1 x2 )  = ((* Id ) (evalB Id x1 ) (evalB Id x2 ) )
  
  evalB Id 0L  = (0ᵢ Id ) 
  
  evalCl : ({A  : Set }  → ((IdempotentSemiRng A ) → ((ClIdempotentSemiRngTerm A ) → A )))
  evalCl Id (sing x1 )  = x1 
  
  evalCl Id (+Cl x1 x2 )  = ((+ Id ) (evalCl Id x1 ) (evalCl Id x2 ) )
  
  evalCl Id (*Cl x1 x2 )  = ((* Id ) (evalCl Id x1 ) (evalCl Id x2 ) )
  
  evalCl Id 0Cl  = (0ᵢ Id ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((IdempotentSemiRng A ) → ((Vec A n ) → ((OpIdempotentSemiRngTerm n ) → A ))))
  evalOp n Id vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Id vars (+OL x1 x2 )  = ((+ Id ) (evalOp n Id vars x1 ) (evalOp n Id vars x2 ) )
  
  evalOp n Id vars (*OL x1 x2 )  = ((* Id ) (evalOp n Id vars x1 ) (evalOp n Id vars x2 ) )
  
  evalOp n Id vars 0OL  = (0ᵢ Id ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((IdempotentSemiRng A ) → ((Vec A n ) → ((OpIdempotentSemiRngTerm2 n A ) → A ))))
  evalOpE n Id vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Id vars (sing2 x1 )  = x1 
  
  evalOpE n Id vars (+OL2 x1 x2 )  = ((+ Id ) (evalOpE n Id vars x1 ) (evalOpE n Id vars x2 ) )
  
  evalOpE n Id vars (*OL2 x1 x2 )  = ((* Id ) (evalOpE n Id vars x1 ) (evalOpE n Id vars x2 ) )
  
  evalOpE n Id vars 0OL2  = (0ᵢ Id ) 
  
  inductionB : ((P  : (IdempotentSemiRngTerm  → Set ))  → (((x1 x2  : IdempotentSemiRngTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1 x2  : IdempotentSemiRngTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P 0L ) → ((x  : IdempotentSemiRngTerm )  → (P x ))))))
  inductionB p p+l p*l p0l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p*l p0l x1 ) (inductionB p p+l p*l p0l x2 ) )
  
  inductionB p p+l p*l p0l (*L x1 x2 )  = (p*l _ _ (inductionB p p+l p*l p0l x1 ) (inductionB p p+l p*l p0l x2 ) )
  
  inductionB p p+l p*l p0l 0L  = p0l 
  
  inductionCl : ((A  : Set ) (P  : ((ClIdempotentSemiRngTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClIdempotentSemiRngTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1 x2  : (ClIdempotentSemiRngTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P 0Cl ) → ((x  : (ClIdempotentSemiRngTerm A ))  → (P x )))))))
  inductionCl _ p psing p+cl p*cl p0cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p*cl p0cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p*cl p0cl x1 ) (inductionCl _ p psing p+cl p*cl p0cl x2 ) )
  
  inductionCl _ p psing p+cl p*cl p0cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p+cl p*cl p0cl x1 ) (inductionCl _ p psing p+cl p*cl p0cl x2 ) )
  
  inductionCl _ p psing p+cl p*cl p0cl 0Cl  = p0cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpIdempotentSemiRngTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpIdempotentSemiRngTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1 x2  : (OpIdempotentSemiRngTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P 0OL ) → ((x  : (OpIdempotentSemiRngTerm n ))  → (P x )))))))
  inductionOp _ p pv p+ol p*ol p0ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p*ol p0ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p*ol p0ol x1 ) (inductionOp _ p pv p+ol p*ol p0ol x2 ) )
  
  inductionOp _ p pv p+ol p*ol p0ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p+ol p*ol p0ol x1 ) (inductionOp _ p pv p+ol p*ol p0ol x2 ) )
  
  inductionOp _ p pv p+ol p*ol p0ol 0OL  = p0ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpIdempotentSemiRngTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpIdempotentSemiRngTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1 x2  : (OpIdempotentSemiRngTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P 0OL2 ) → ((x  : (OpIdempotentSemiRngTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 p0ol2 0OL2  = p0ol2 
  
  +L' : (  (IdempotentSemiRngTerm   → (IdempotentSemiRngTerm   → IdempotentSemiRngTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  *L' : (  (IdempotentSemiRngTerm   → (IdempotentSemiRngTerm   → IdempotentSemiRngTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  0L' : (  IdempotentSemiRngTerm  )
  0L'  = 0L 
  
  stageB : (IdempotentSemiRngTerm  → (Staged IdempotentSemiRngTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 0L  = (Now 0L )
  
  +Cl' : ({A  : Set }  → ((ClIdempotentSemiRngTerm A )  → ((ClIdempotentSemiRngTerm A )  → (ClIdempotentSemiRngTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  *Cl' : ({A  : Set }  → ((ClIdempotentSemiRngTerm A )  → ((ClIdempotentSemiRngTerm A )  → (ClIdempotentSemiRngTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  0Cl' : ({A  : Set }  → (ClIdempotentSemiRngTerm A ) )
  0Cl'  = 0Cl 
  
  stageCl : ((A  : Set )  → ((ClIdempotentSemiRngTerm A ) → (Staged (ClIdempotentSemiRngTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  +OL' : ({n  : Nat}  → ((OpIdempotentSemiRngTerm n )  → ((OpIdempotentSemiRngTerm n )  → (OpIdempotentSemiRngTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  *OL' : ({n  : Nat}  → ((OpIdempotentSemiRngTerm n )  → ((OpIdempotentSemiRngTerm n )  → (OpIdempotentSemiRngTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  0OL' : ({n  : Nat}  → (OpIdempotentSemiRngTerm n ) )
  0OL'  = 0OL 
  
  stageOp : ((n  : Nat)  → ((OpIdempotentSemiRngTerm n ) → (Staged (OpIdempotentSemiRngTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpIdempotentSemiRngTerm2 n A )  → ((OpIdempotentSemiRngTerm2 n A )  → (OpIdempotentSemiRngTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpIdempotentSemiRngTerm2 n A )  → ((OpIdempotentSemiRngTerm2 n A )  → (OpIdempotentSemiRngTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpIdempotentSemiRngTerm2 n A ) )
  0OL2'  = 0OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentSemiRngTerm2 n A ) → (Staged (OpIdempotentSemiRngTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      0T : (Repr A )  
   
