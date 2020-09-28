module DualSemilattices  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record DualSemilattices (A  : Set )  : Set where
    constructor DualSemilatticesC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      idempotent_* : ({x  : A }  → (* x x ) ≡ x )
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
  open DualSemilattices
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      idempotent_*P : ({xP  : (Prod AP AP )}  → (*P xP xP ) ≡ xP )
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP ))
      associative_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P xP yP ) zP ) ≡ (+P xP (+P yP zP ) ))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP )
  record Hom (A1 A2  : Set ) (Du1  : (DualSemilattices A1 )) (Du2  : (DualSemilattices A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Du1 ) x1 x2 ) ) ≡ ((* Du2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Du1 ) x1 x2 ) ) ≡ ((+ Du2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Du1  : (DualSemilattices A1 )) (Du2  : (DualSemilattices A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Du1 ) x1 x2 ) ((* Du2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Du1 ) x1 x2 ) ((+ Du2 ) y1 y2 ) ))))
  data DualSemilatticesTerm  : Set where
    *L : (DualSemilatticesTerm   → (DualSemilatticesTerm   → DualSemilatticesTerm  ))
    +L : (DualSemilatticesTerm   → (DualSemilatticesTerm   → DualSemilatticesTerm  ))
  data ClDualSemilatticesTerm (A  : Set )  : Set where
    sing : (A  → (ClDualSemilatticesTerm A ) )
    *Cl : ((ClDualSemilatticesTerm A )  → ((ClDualSemilatticesTerm A )  → (ClDualSemilatticesTerm A ) ))
    +Cl : ((ClDualSemilatticesTerm A )  → ((ClDualSemilatticesTerm A )  → (ClDualSemilatticesTerm A ) ))
  data OpDualSemilatticesTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpDualSemilatticesTerm n ) )
    *OL : ((OpDualSemilatticesTerm n )  → ((OpDualSemilatticesTerm n )  → (OpDualSemilatticesTerm n ) ))
    +OL : ((OpDualSemilatticesTerm n )  → ((OpDualSemilatticesTerm n )  → (OpDualSemilatticesTerm n ) ))
  data OpDualSemilatticesTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpDualSemilatticesTerm2 n A ) )
    sing2 : (A  → (OpDualSemilatticesTerm2 n A ) )
    *OL2 : ((OpDualSemilatticesTerm2 n A )  → ((OpDualSemilatticesTerm2 n A )  → (OpDualSemilatticesTerm2 n A ) ))
    +OL2 : ((OpDualSemilatticesTerm2 n A )  → ((OpDualSemilatticesTerm2 n A )  → (OpDualSemilatticesTerm2 n A ) ))
  evalB : ({A  : Set }  → ((DualSemilattices A ) → (DualSemilatticesTerm  → A )))
  evalB Du (*L x1 x2 )  = ((* Du ) (evalB Du x1 ) (evalB Du x2 ) )
  
  evalB Du (+L x1 x2 )  = ((+ Du ) (evalB Du x1 ) (evalB Du x2 ) )
  
  evalCl : ({A  : Set }  → ((DualSemilattices A ) → ((ClDualSemilatticesTerm A ) → A )))
  evalCl Du (sing x1 )  = x1 
  
  evalCl Du (*Cl x1 x2 )  = ((* Du ) (evalCl Du x1 ) (evalCl Du x2 ) )
  
  evalCl Du (+Cl x1 x2 )  = ((+ Du ) (evalCl Du x1 ) (evalCl Du x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((DualSemilattices A ) → ((Vec A n ) → ((OpDualSemilatticesTerm n ) → A ))))
  evalOp n Du vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Du vars (*OL x1 x2 )  = ((* Du ) (evalOp n Du vars x1 ) (evalOp n Du vars x2 ) )
  
  evalOp n Du vars (+OL x1 x2 )  = ((+ Du ) (evalOp n Du vars x1 ) (evalOp n Du vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((DualSemilattices A ) → ((Vec A n ) → ((OpDualSemilatticesTerm2 n A ) → A ))))
  evalOpE n Du vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Du vars (sing2 x1 )  = x1 
  
  evalOpE n Du vars (*OL2 x1 x2 )  = ((* Du ) (evalOpE n Du vars x1 ) (evalOpE n Du vars x2 ) )
  
  evalOpE n Du vars (+OL2 x1 x2 )  = ((+ Du ) (evalOpE n Du vars x1 ) (evalOpE n Du vars x2 ) )
  
  inductionB : ((P  : (DualSemilatticesTerm  → Set ))  → (((x1 x2  : DualSemilatticesTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : DualSemilatticesTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : DualSemilatticesTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClDualSemilatticesTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClDualSemilatticesTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClDualSemilatticesTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClDualSemilatticesTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpDualSemilatticesTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpDualSemilatticesTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpDualSemilatticesTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpDualSemilatticesTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpDualSemilatticesTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpDualSemilatticesTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpDualSemilatticesTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpDualSemilatticesTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (DualSemilatticesTerm   → (DualSemilatticesTerm   → DualSemilatticesTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (DualSemilatticesTerm   → (DualSemilatticesTerm   → DualSemilatticesTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (DualSemilatticesTerm  → (Staged DualSemilatticesTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClDualSemilatticesTerm A )  → ((ClDualSemilatticesTerm A )  → (ClDualSemilatticesTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClDualSemilatticesTerm A )  → ((ClDualSemilatticesTerm A )  → (ClDualSemilatticesTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClDualSemilatticesTerm A ) → (Staged (ClDualSemilatticesTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpDualSemilatticesTerm n )  → ((OpDualSemilatticesTerm n )  → (OpDualSemilatticesTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpDualSemilatticesTerm n )  → ((OpDualSemilatticesTerm n )  → (OpDualSemilatticesTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpDualSemilatticesTerm n ) → (Staged (OpDualSemilatticesTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpDualSemilatticesTerm2 n A )  → ((OpDualSemilatticesTerm2 n A )  → (OpDualSemilatticesTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpDualSemilatticesTerm2 n A )  → ((OpDualSemilatticesTerm2 n A )  → (OpDualSemilatticesTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpDualSemilatticesTerm2 n A ) → (Staged (OpDualSemilatticesTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))