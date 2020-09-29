
 module MultMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultMonoid (A  : Set )  : Set where
    constructor MultMonoidC
    field
      1ᵢ : A 
      * : (A  → (A  → A ))
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) )) 
  
  open MultMonoid
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      1S : AS 
      *S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      1P : (Prod AP AP )
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) )) 
  
  record Hom (A1 A2  : Set ) (Mu1  : (MultMonoid A1 )) (Mu2  : (MultMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-1 : (  (hom (1ᵢ Mu1 )  ) ≡ (1ᵢ Mu2 ) )
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Mu1 ) x1 x2 ) ) ≡ ((* Mu2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mu1  : (MultMonoid A1 )) (Mu2  : (MultMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-1 : (  (interp (1ᵢ Mu1 )  (1ᵢ Mu2 )  ))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Mu1 ) x1 x2 ) ((* Mu2 ) y1 y2 ) )))) 
  
  data MultMonoidTerm  : Set where
    1L : MultMonoidTerm  
    *L : (MultMonoidTerm   → (MultMonoidTerm   → MultMonoidTerm  )) 
  
  data ClMultMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClMultMonoidTerm A ) )
    1Cl : (ClMultMonoidTerm A ) 
    *Cl : ((ClMultMonoidTerm A )  → ((ClMultMonoidTerm A )  → (ClMultMonoidTerm A ) )) 
  
  data OpMultMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMultMonoidTerm n ) )
    1OL : (OpMultMonoidTerm n ) 
    *OL : ((OpMultMonoidTerm n )  → ((OpMultMonoidTerm n )  → (OpMultMonoidTerm n ) )) 
  
  data OpMultMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMultMonoidTerm2 n A ) )
    sing2 : (A  → (OpMultMonoidTerm2 n A ) )
    1OL2 : (OpMultMonoidTerm2 n A ) 
    *OL2 : ((OpMultMonoidTerm2 n A )  → ((OpMultMonoidTerm2 n A )  → (OpMultMonoidTerm2 n A ) )) 
  
  simplifyB : (MultMonoidTerm  → MultMonoidTerm )
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB 1L  = 1L 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMultMonoidTerm A ) → (ClMultMonoidTerm A )))
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMultMonoidTerm n ) → (OpMultMonoidTerm n )))
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMultMonoidTerm2 n A ) → (OpMultMonoidTerm2 n A )))
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MultMonoid A ) → (MultMonoidTerm  → A )))
  evalB Mu 1L  = (1ᵢ Mu ) 
  
  evalB Mu (*L x1 x2 )  = ((* Mu ) (evalB Mu x1 ) (evalB Mu x2 ) )
  
  evalCl : ({A  : Set }  → ((MultMonoid A ) → ((ClMultMonoidTerm A ) → A )))
  evalCl Mu (sing x1 )  = x1 
  
  evalCl Mu 1Cl  = (1ᵢ Mu ) 
  
  evalCl Mu (*Cl x1 x2 )  = ((* Mu ) (evalCl Mu x1 ) (evalCl Mu x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MultMonoid A ) → ((Vec A n ) → ((OpMultMonoidTerm n ) → A ))))
  evalOp n Mu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mu vars 1OL  = (1ᵢ Mu ) 
  
  evalOp n Mu vars (*OL x1 x2 )  = ((* Mu ) (evalOp n Mu vars x1 ) (evalOp n Mu vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MultMonoid A ) → ((Vec A n ) → ((OpMultMonoidTerm2 n A ) → A ))))
  evalOpE n Mu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mu vars (sing2 x1 )  = x1 
  
  evalOpE n Mu vars 1OL2  = (1ᵢ Mu ) 
  
  evalOpE n Mu vars (*OL2 x1 x2 )  = ((* Mu ) (evalOpE n Mu vars x1 ) (evalOpE n Mu vars x2 ) )
  
  inductionB : ((P  : (MultMonoidTerm  → Set ))  → ((P 1L ) → (((x1 x2  : MultMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : MultMonoidTerm )  → (P x )))))
  inductionB p p1l p*l 1L  = p1l 
  
  inductionB p p1l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p1l p*l x1 ) (inductionB p p1l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMultMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 1Cl ) → (((x1 x2  : (ClMultMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClMultMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing p1cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p1cl p*cl 1Cl  = p1cl 
  
  inductionCl _ p psing p1cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p1cl p*cl x1 ) (inductionCl _ p psing p1cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMultMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 1OL ) → (((x1 x2  : (OpMultMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpMultMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv p1ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p1ol p*ol 1OL  = p1ol 
  
  inductionOp _ p pv p1ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p1ol p*ol x1 ) (inductionOp _ p pv p1ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMultMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 1OL2 ) → (((x1 x2  : (OpMultMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpMultMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 x2 ) )
  
  1L' : (  MultMonoidTerm  )
  1L'  = 1L 
  
  *L' : (  (MultMonoidTerm   → (MultMonoidTerm   → MultMonoidTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (MultMonoidTerm  → (Staged MultMonoidTerm  ))
  stageB 1L  = (Now 1L )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  1Cl' : ({A  : Set }  → (ClMultMonoidTerm A ) )
  1Cl'  = 1Cl 
  
  *Cl' : ({A  : Set }  → ((ClMultMonoidTerm A )  → ((ClMultMonoidTerm A )  → (ClMultMonoidTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMultMonoidTerm A ) → (Staged (ClMultMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  1OL' : ({n  : Nat}  → (OpMultMonoidTerm n ) )
  1OL'  = 1OL 
  
  *OL' : ({n  : Nat}  → ((OpMultMonoidTerm n )  → ((OpMultMonoidTerm n )  → (OpMultMonoidTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMultMonoidTerm n ) → (Staged (OpMultMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpMultMonoidTerm2 n A ) )
  1OL2'  = 1OL2 
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpMultMonoidTerm2 n A )  → ((OpMultMonoidTerm2 n A )  → (OpMultMonoidTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMultMonoidTerm2 n A ) → (Staged (OpMultMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      1T : (Repr A ) 
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
