
 module Lattice  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Lattice (A  : Set )  : Set where
    constructor LatticeC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      idempotent_* : ({x  : A }  → (* x x ) ≡ x )
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x ))
      associative_+ : ({x y z  : A }  → (+ (+ x y ) z ) ≡ (+ x (+ y z ) ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
      leftAbsorp_*_+ : ({x y  : A }  → (* x (+ x y ) ) ≡ x )
      leftAbsorp_+_* : ({x y  : A }  → (+ x (* x y ) ) ≡ x ) 
  
  open Lattice
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
      leftAbsorp_*_+P : ({xP yP  : (Prod AP AP )}  → (*P xP (+P xP yP ) ) ≡ xP )
      leftAbsorp_+_*P : ({xP yP  : (Prod AP AP )}  → (+P xP (*P xP yP ) ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (La1  : (Lattice A1 )) (La2  : (Lattice A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* La1 ) x1 x2 ) ) ≡ ((* La2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ La1 ) x1 x2 ) ) ≡ ((+ La2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (La1  : (Lattice A1 )) (La2  : (Lattice A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* La1 ) x1 x2 ) ((* La2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ La1 ) x1 x2 ) ((+ La2 ) y1 y2 ) )))) 
  
  data LatticeTerm  : Set where
    *L : (LatticeTerm   → (LatticeTerm   → LatticeTerm  ))
    +L : (LatticeTerm   → (LatticeTerm   → LatticeTerm  )) 
  
  data ClLatticeTerm (A  : Set )  : Set where
    sing : (A  → (ClLatticeTerm A ) )
    *Cl : ((ClLatticeTerm A )  → ((ClLatticeTerm A )  → (ClLatticeTerm A ) ))
    +Cl : ((ClLatticeTerm A )  → ((ClLatticeTerm A )  → (ClLatticeTerm A ) )) 
  
  data OpLatticeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLatticeTerm n ) )
    *OL : ((OpLatticeTerm n )  → ((OpLatticeTerm n )  → (OpLatticeTerm n ) ))
    +OL : ((OpLatticeTerm n )  → ((OpLatticeTerm n )  → (OpLatticeTerm n ) )) 
  
  data OpLatticeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLatticeTerm2 n A ) )
    sing2 : (A  → (OpLatticeTerm2 n A ) )
    *OL2 : ((OpLatticeTerm2 n A )  → ((OpLatticeTerm2 n A )  → (OpLatticeTerm2 n A ) ))
    +OL2 : ((OpLatticeTerm2 n A )  → ((OpLatticeTerm2 n A )  → (OpLatticeTerm2 n A ) )) 
  
  simplifyB : (LatticeTerm  → LatticeTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClLatticeTerm A ) → (ClLatticeTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpLatticeTerm n ) → (OpLatticeTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpLatticeTerm2 n A ) → (OpLatticeTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Lattice A ) → (LatticeTerm  → A )))
  evalB La (*L x1 x2 )  = ((* La ) (evalB La x1 ) (evalB La x2 ) )
  
  evalB La (+L x1 x2 )  = ((+ La ) (evalB La x1 ) (evalB La x2 ) )
  
  evalCl : ({A  : Set }  → ((Lattice A ) → ((ClLatticeTerm A ) → A )))
  evalCl La (sing x1 )  = x1 
  
  evalCl La (*Cl x1 x2 )  = ((* La ) (evalCl La x1 ) (evalCl La x2 ) )
  
  evalCl La (+Cl x1 x2 )  = ((+ La ) (evalCl La x1 ) (evalCl La x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Lattice A ) → ((Vec A n ) → ((OpLatticeTerm n ) → A ))))
  evalOp n La vars (v x1 )  = (lookup vars x1 )
  
  evalOp n La vars (*OL x1 x2 )  = ((* La ) (evalOp n La vars x1 ) (evalOp n La vars x2 ) )
  
  evalOp n La vars (+OL x1 x2 )  = ((+ La ) (evalOp n La vars x1 ) (evalOp n La vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Lattice A ) → ((Vec A n ) → ((OpLatticeTerm2 n A ) → A ))))
  evalOpE n La vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n La vars (sing2 x1 )  = x1 
  
  evalOpE n La vars (*OL2 x1 x2 )  = ((* La ) (evalOpE n La vars x1 ) (evalOpE n La vars x2 ) )
  
  evalOpE n La vars (+OL2 x1 x2 )  = ((+ La ) (evalOpE n La vars x1 ) (evalOpE n La vars x2 ) )
  
  inductionB : ((P  : (LatticeTerm  → Set ))  → (((x1 x2  : LatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : LatticeTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : LatticeTerm )  → (P x )))))
  inductionB p p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionB p p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l x1 ) (inductionB p p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLatticeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClLatticeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClLatticeTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1 ) (inductionCl _ p psing p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLatticeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpLatticeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpLatticeTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol x1 ) (inductionOp _ p pv p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLatticeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpLatticeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpLatticeTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 x2 ) )
  
  *L' : (  (LatticeTerm   → (LatticeTerm   → LatticeTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (LatticeTerm   → (LatticeTerm   → LatticeTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (LatticeTerm  → (Staged LatticeTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClLatticeTerm A )  → ((ClLatticeTerm A )  → (ClLatticeTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClLatticeTerm A )  → ((ClLatticeTerm A )  → (ClLatticeTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLatticeTerm A ) → (Staged (ClLatticeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpLatticeTerm n )  → ((OpLatticeTerm n )  → (OpLatticeTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpLatticeTerm n )  → ((OpLatticeTerm n )  → (OpLatticeTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLatticeTerm n ) → (Staged (OpLatticeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpLatticeTerm2 n A )  → ((OpLatticeTerm2 n A )  → (OpLatticeTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpLatticeTerm2 n A )  → ((OpLatticeTerm2 n A )  → (OpLatticeTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLatticeTerm2 n A ) → (Staged (OpLatticeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
