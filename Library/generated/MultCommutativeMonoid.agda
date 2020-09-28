module MultCommutativeMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultCommutativeMonoid (A  : Set )  : Set where
    constructor MultCommutativeMonoidC
    field
      * : (A  → (A  → A ))
      1ᵢ : A 
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
  open MultCommutativeMonoid
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
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP ))
  record Hom (A1 A2  : Set ) (Mu1  : (MultCommutativeMonoid A1 )) (Mu2  : (MultCommutativeMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Mu1 ) x1 x2 ) ) ≡ ((* Mu2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Mu1 )  ) ≡ (1ᵢ Mu2 ) )
  record RelInterp (A1 A2  : Set ) (Mu1  : (MultCommutativeMonoid A1 )) (Mu2  : (MultCommutativeMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Mu1 ) x1 x2 ) ((* Mu2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Mu1 )  (1ᵢ Mu2 )  ))
  data MultCommutativeMonoidTerm  : Set where
    *L : (MultCommutativeMonoidTerm   → (MultCommutativeMonoidTerm   → MultCommutativeMonoidTerm  ))
    1L : MultCommutativeMonoidTerm  
  data ClMultCommutativeMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClMultCommutativeMonoidTerm A ) )
    *Cl : ((ClMultCommutativeMonoidTerm A )  → ((ClMultCommutativeMonoidTerm A )  → (ClMultCommutativeMonoidTerm A ) ))
    1Cl : (ClMultCommutativeMonoidTerm A ) 
  data OpMultCommutativeMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMultCommutativeMonoidTerm n ) )
    *OL : ((OpMultCommutativeMonoidTerm n )  → ((OpMultCommutativeMonoidTerm n )  → (OpMultCommutativeMonoidTerm n ) ))
    1OL : (OpMultCommutativeMonoidTerm n ) 
  data OpMultCommutativeMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMultCommutativeMonoidTerm2 n A ) )
    sing2 : (A  → (OpMultCommutativeMonoidTerm2 n A ) )
    *OL2 : ((OpMultCommutativeMonoidTerm2 n A )  → ((OpMultCommutativeMonoidTerm2 n A )  → (OpMultCommutativeMonoidTerm2 n A ) ))
    1OL2 : (OpMultCommutativeMonoidTerm2 n A ) 
  evalB : ({A  : Set }  → ((MultCommutativeMonoid A ) → (MultCommutativeMonoidTerm  → A )))
  evalB Mu (*L x1 x2 )  = ((* Mu ) (evalB Mu x1 ) (evalB Mu x2 ) )
  
  evalB Mu 1L  = (1ᵢ Mu ) 
  
  evalCl : ({A  : Set }  → ((MultCommutativeMonoid A ) → ((ClMultCommutativeMonoidTerm A ) → A )))
  evalCl Mu (sing x1 )  = x1 
  
  evalCl Mu (*Cl x1 x2 )  = ((* Mu ) (evalCl Mu x1 ) (evalCl Mu x2 ) )
  
  evalCl Mu 1Cl  = (1ᵢ Mu ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MultCommutativeMonoid A ) → ((Vec A n ) → ((OpMultCommutativeMonoidTerm n ) → A ))))
  evalOp n Mu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mu vars (*OL x1 x2 )  = ((* Mu ) (evalOp n Mu vars x1 ) (evalOp n Mu vars x2 ) )
  
  evalOp n Mu vars 1OL  = (1ᵢ Mu ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MultCommutativeMonoid A ) → ((Vec A n ) → ((OpMultCommutativeMonoidTerm2 n A ) → A ))))
  evalOpE n Mu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mu vars (sing2 x1 )  = x1 
  
  evalOpE n Mu vars (*OL2 x1 x2 )  = ((* Mu ) (evalOpE n Mu vars x1 ) (evalOpE n Mu vars x2 ) )
  
  evalOpE n Mu vars 1OL2  = (1ᵢ Mu ) 
  
  inductionB : ((P  : (MultCommutativeMonoidTerm  → Set ))  → (((x1 x2  : MultCommutativeMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P 1L ) → ((x  : MultCommutativeMonoidTerm )  → (P x )))))
  inductionB p p*l p1l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p1l x1 ) (inductionB p p*l p1l x2 ) )
  
  inductionB p p*l p1l 1L  = p1l 
  
  inductionCl : ((A  : Set ) (P  : ((ClMultCommutativeMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMultCommutativeMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P 1Cl ) → ((x  : (ClMultCommutativeMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl p1cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p1cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p1cl x1 ) (inductionCl _ p psing p*cl p1cl x2 ) )
  
  inductionCl _ p psing p*cl p1cl 1Cl  = p1cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpMultCommutativeMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMultCommutativeMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P 1OL ) → ((x  : (OpMultCommutativeMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol p1ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p1ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p1ol x1 ) (inductionOp _ p pv p*ol p1ol x2 ) )
  
  inductionOp _ p pv p*ol p1ol 1OL  = p1ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMultCommutativeMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMultCommutativeMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P 1OL2 ) → ((x  : (OpMultCommutativeMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 1OL2  = p1ol2 
  
  *L' : (  (MultCommutativeMonoidTerm   → (MultCommutativeMonoidTerm   → MultCommutativeMonoidTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  1L' : (  MultCommutativeMonoidTerm  )
  1L'  = 1L 
  
  stageB : (MultCommutativeMonoidTerm  → (Staged MultCommutativeMonoidTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  *Cl' : ({A  : Set }  → ((ClMultCommutativeMonoidTerm A )  → ((ClMultCommutativeMonoidTerm A )  → (ClMultCommutativeMonoidTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClMultCommutativeMonoidTerm A ) )
  1Cl'  = 1Cl 
  
  stageCl : ((A  : Set )  → ((ClMultCommutativeMonoidTerm A ) → (Staged (ClMultCommutativeMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  *OL' : ({n  : Nat}  → ((OpMultCommutativeMonoidTerm n )  → ((OpMultCommutativeMonoidTerm n )  → (OpMultCommutativeMonoidTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpMultCommutativeMonoidTerm n ) )
  1OL'  = 1OL 
  
  stageOp : ((n  : Nat)  → ((OpMultCommutativeMonoidTerm n ) → (Staged (OpMultCommutativeMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpMultCommutativeMonoidTerm2 n A )  → ((OpMultCommutativeMonoidTerm2 n A )  → (OpMultCommutativeMonoidTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpMultCommutativeMonoidTerm2 n A ) )
  1OL2'  = 1OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMultCommutativeMonoidTerm2 n A ) → (Staged (OpMultCommutativeMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 