module NonDistributiveAddPreSemiring  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record NonDistributiveAddPreSemiring (A  : Set )  : Set where
    constructor NonDistributiveAddPreSemiringC
    field
      + : (A  → (A  → A ))
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      * : (A  → (A  → A ))
  open NonDistributiveAddPreSemiring
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      *S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
  record Hom (A1 A2  : Set ) (No1  : (NonDistributiveAddPreSemiring A1 )) (No2  : (NonDistributiveAddPreSemiring A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ No1 ) x1 x2 ) ) ≡ ((+ No2 ) (hom x1 ) (hom x2 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* No1 ) x1 x2 ) ) ≡ ((* No2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (No1  : (NonDistributiveAddPreSemiring A1 )) (No2  : (NonDistributiveAddPreSemiring A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ No1 ) x1 x2 ) ((+ No2 ) y1 y2 ) ))))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* No1 ) x1 x2 ) ((* No2 ) y1 y2 ) ))))
  data NonDistributiveAddPreSemiringTerm  : Set where
    +L : (NonDistributiveAddPreSemiringTerm   → (NonDistributiveAddPreSemiringTerm   → NonDistributiveAddPreSemiringTerm  ))
    *L : (NonDistributiveAddPreSemiringTerm   → (NonDistributiveAddPreSemiringTerm   → NonDistributiveAddPreSemiringTerm  ))
  data ClNonDistributiveAddPreSemiringTerm (A  : Set )  : Set where
    sing : (A  → (ClNonDistributiveAddPreSemiringTerm A ) )
    +Cl : ((ClNonDistributiveAddPreSemiringTerm A )  → ((ClNonDistributiveAddPreSemiringTerm A )  → (ClNonDistributiveAddPreSemiringTerm A ) ))
    *Cl : ((ClNonDistributiveAddPreSemiringTerm A )  → ((ClNonDistributiveAddPreSemiringTerm A )  → (ClNonDistributiveAddPreSemiringTerm A ) ))
  data OpNonDistributiveAddPreSemiringTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpNonDistributiveAddPreSemiringTerm n ) )
    +OL : ((OpNonDistributiveAddPreSemiringTerm n )  → ((OpNonDistributiveAddPreSemiringTerm n )  → (OpNonDistributiveAddPreSemiringTerm n ) ))
    *OL : ((OpNonDistributiveAddPreSemiringTerm n )  → ((OpNonDistributiveAddPreSemiringTerm n )  → (OpNonDistributiveAddPreSemiringTerm n ) ))
  data OpNonDistributiveAddPreSemiringTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpNonDistributiveAddPreSemiringTerm2 n A ) )
    sing2 : (A  → (OpNonDistributiveAddPreSemiringTerm2 n A ) )
    +OL2 : ((OpNonDistributiveAddPreSemiringTerm2 n A )  → ((OpNonDistributiveAddPreSemiringTerm2 n A )  → (OpNonDistributiveAddPreSemiringTerm2 n A ) ))
    *OL2 : ((OpNonDistributiveAddPreSemiringTerm2 n A )  → ((OpNonDistributiveAddPreSemiringTerm2 n A )  → (OpNonDistributiveAddPreSemiringTerm2 n A ) ))
  evalB : ({A  : Set }  → ((NonDistributiveAddPreSemiring A ) → (NonDistributiveAddPreSemiringTerm  → A )))
  evalB No (+L x1 x2 )  = ((+ No ) (evalB No x1 ) (evalB No x2 ) )
  
  evalB No (*L x1 x2 )  = ((* No ) (evalB No x1 ) (evalB No x2 ) )
  
  evalCl : ({A  : Set }  → ((NonDistributiveAddPreSemiring A ) → ((ClNonDistributiveAddPreSemiringTerm A ) → A )))
  evalCl No (sing x1 )  = x1 
  
  evalCl No (+Cl x1 x2 )  = ((+ No ) (evalCl No x1 ) (evalCl No x2 ) )
  
  evalCl No (*Cl x1 x2 )  = ((* No ) (evalCl No x1 ) (evalCl No x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((NonDistributiveAddPreSemiring A ) → ((Vec A n ) → ((OpNonDistributiveAddPreSemiringTerm n ) → A ))))
  evalOp n No vars (v x1 )  = (lookup vars x1 )
  
  evalOp n No vars (+OL x1 x2 )  = ((+ No ) (evalOp n No vars x1 ) (evalOp n No vars x2 ) )
  
  evalOp n No vars (*OL x1 x2 )  = ((* No ) (evalOp n No vars x1 ) (evalOp n No vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((NonDistributiveAddPreSemiring A ) → ((Vec A n ) → ((OpNonDistributiveAddPreSemiringTerm2 n A ) → A ))))
  evalOpE n No vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n No vars (sing2 x1 )  = x1 
  
  evalOpE n No vars (+OL2 x1 x2 )  = ((+ No ) (evalOpE n No vars x1 ) (evalOpE n No vars x2 ) )
  
  evalOpE n No vars (*OL2 x1 x2 )  = ((* No ) (evalOpE n No vars x1 ) (evalOpE n No vars x2 ) )
  
  inductionB : ((P  : (NonDistributiveAddPreSemiringTerm  → Set ))  → (((x1 x2  : NonDistributiveAddPreSemiringTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1 x2  : NonDistributiveAddPreSemiringTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : NonDistributiveAddPreSemiringTerm )  → (P x )))))
  inductionB p p+l p*l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l p*l x1 ) (inductionB p p+l p*l x2 ) )
  
  inductionB p p+l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p+l p*l x1 ) (inductionB p p+l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClNonDistributiveAddPreSemiringTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClNonDistributiveAddPreSemiringTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1 x2  : (ClNonDistributiveAddPreSemiringTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClNonDistributiveAddPreSemiringTerm A ))  → (P x ))))))
  inductionCl _ p psing p+cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl p*cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl p*cl x1 ) (inductionCl _ p psing p+cl p*cl x2 ) )
  
  inductionCl _ p psing p+cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p+cl p*cl x1 ) (inductionCl _ p psing p+cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpNonDistributiveAddPreSemiringTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpNonDistributiveAddPreSemiringTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1 x2  : (OpNonDistributiveAddPreSemiringTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpNonDistributiveAddPreSemiringTerm n ))  → (P x ))))))
  inductionOp _ p pv p+ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol p*ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol p*ol x1 ) (inductionOp _ p pv p+ol p*ol x2 ) )
  
  inductionOp _ p pv p+ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p+ol p*ol x1 ) (inductionOp _ p pv p+ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpNonDistributiveAddPreSemiringTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpNonDistributiveAddPreSemiringTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1 x2  : (OpNonDistributiveAddPreSemiringTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpNonDistributiveAddPreSemiringTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 p*ol2 x2 ) )
  
  +L' : (  (NonDistributiveAddPreSemiringTerm   → (NonDistributiveAddPreSemiringTerm   → NonDistributiveAddPreSemiringTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  *L' : (  (NonDistributiveAddPreSemiringTerm   → (NonDistributiveAddPreSemiringTerm   → NonDistributiveAddPreSemiringTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (NonDistributiveAddPreSemiringTerm  → (Staged NonDistributiveAddPreSemiringTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClNonDistributiveAddPreSemiringTerm A )  → ((ClNonDistributiveAddPreSemiringTerm A )  → (ClNonDistributiveAddPreSemiringTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  *Cl' : ({A  : Set }  → ((ClNonDistributiveAddPreSemiringTerm A )  → ((ClNonDistributiveAddPreSemiringTerm A )  → (ClNonDistributiveAddPreSemiringTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClNonDistributiveAddPreSemiringTerm A ) → (Staged (ClNonDistributiveAddPreSemiringTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpNonDistributiveAddPreSemiringTerm n )  → ((OpNonDistributiveAddPreSemiringTerm n )  → (OpNonDistributiveAddPreSemiringTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  *OL' : ({n  : Nat}  → ((OpNonDistributiveAddPreSemiringTerm n )  → ((OpNonDistributiveAddPreSemiringTerm n )  → (OpNonDistributiveAddPreSemiringTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpNonDistributiveAddPreSemiringTerm n ) → (Staged (OpNonDistributiveAddPreSemiringTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpNonDistributiveAddPreSemiringTerm2 n A )  → ((OpNonDistributiveAddPreSemiringTerm2 n A )  → (OpNonDistributiveAddPreSemiringTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpNonDistributiveAddPreSemiringTerm2 n A )  → ((OpNonDistributiveAddPreSemiringTerm2 n A )  → (OpNonDistributiveAddPreSemiringTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpNonDistributiveAddPreSemiringTerm2 n A ) → (Staged (OpNonDistributiveAddPreSemiringTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))