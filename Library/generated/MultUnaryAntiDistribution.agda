module MultUnaryAntiDistribution  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultUnaryAntiDistribution (A  : Set )  : Set where
    constructor MultUnaryAntiDistributionC
    field
      prim : (A  → A )
      * : (A  → (A  → A ))
      antidis_prim_* : ({x y  : A }  → (prim (* x y ) ) ≡ (* (prim y ) (prim x ) ))
  open MultUnaryAntiDistribution
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      *S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      antidis_prim_*P : ({xP yP  : (Prod AP AP )}  → (primP (*P xP yP ) ) ≡ (*P (primP yP ) (primP xP ) ))
  record Hom (A1 A2  : Set ) (Mu1  : (MultUnaryAntiDistribution A1 )) (Mu2  : (MultUnaryAntiDistribution A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Mu1 ) x1 ) ) ≡ ((prim Mu2 ) (hom x1 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Mu1 ) x1 x2 ) ) ≡ ((* Mu2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Mu1  : (MultUnaryAntiDistribution A1 )) (Mu2  : (MultUnaryAntiDistribution A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Mu1 ) x1 ) ((prim Mu2 ) y1 ) )))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Mu1 ) x1 x2 ) ((* Mu2 ) y1 y2 ) ))))
  data MultUnaryAntiDistributionTerm  : Set where
    primL : (MultUnaryAntiDistributionTerm   → MultUnaryAntiDistributionTerm  )
    *L : (MultUnaryAntiDistributionTerm   → (MultUnaryAntiDistributionTerm   → MultUnaryAntiDistributionTerm  ))
  data ClMultUnaryAntiDistributionTerm (A  : Set )  : Set where
    sing : (A  → (ClMultUnaryAntiDistributionTerm A ) )
    primCl : ((ClMultUnaryAntiDistributionTerm A )  → (ClMultUnaryAntiDistributionTerm A ) )
    *Cl : ((ClMultUnaryAntiDistributionTerm A )  → ((ClMultUnaryAntiDistributionTerm A )  → (ClMultUnaryAntiDistributionTerm A ) ))
  data OpMultUnaryAntiDistributionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMultUnaryAntiDistributionTerm n ) )
    primOL : ((OpMultUnaryAntiDistributionTerm n )  → (OpMultUnaryAntiDistributionTerm n ) )
    *OL : ((OpMultUnaryAntiDistributionTerm n )  → ((OpMultUnaryAntiDistributionTerm n )  → (OpMultUnaryAntiDistributionTerm n ) ))
  data OpMultUnaryAntiDistributionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMultUnaryAntiDistributionTerm2 n A ) )
    sing2 : (A  → (OpMultUnaryAntiDistributionTerm2 n A ) )
    primOL2 : ((OpMultUnaryAntiDistributionTerm2 n A )  → (OpMultUnaryAntiDistributionTerm2 n A ) )
    *OL2 : ((OpMultUnaryAntiDistributionTerm2 n A )  → ((OpMultUnaryAntiDistributionTerm2 n A )  → (OpMultUnaryAntiDistributionTerm2 n A ) ))
  evalB : ({A  : Set }  → ((MultUnaryAntiDistribution A ) → (MultUnaryAntiDistributionTerm  → A )))
  evalB Mu (primL x1 )  = ((prim Mu ) (evalB Mu x1 ) )
  
  evalB Mu (*L x1 x2 )  = ((* Mu ) (evalB Mu x1 ) (evalB Mu x2 ) )
  
  evalCl : ({A  : Set }  → ((MultUnaryAntiDistribution A ) → ((ClMultUnaryAntiDistributionTerm A ) → A )))
  evalCl Mu (sing x1 )  = x1 
  
  evalCl Mu (primCl x1 )  = ((prim Mu ) (evalCl Mu x1 ) )
  
  evalCl Mu (*Cl x1 x2 )  = ((* Mu ) (evalCl Mu x1 ) (evalCl Mu x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MultUnaryAntiDistribution A ) → ((Vec A n ) → ((OpMultUnaryAntiDistributionTerm n ) → A ))))
  evalOp n Mu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mu vars (primOL x1 )  = ((prim Mu ) (evalOp n Mu vars x1 ) )
  
  evalOp n Mu vars (*OL x1 x2 )  = ((* Mu ) (evalOp n Mu vars x1 ) (evalOp n Mu vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MultUnaryAntiDistribution A ) → ((Vec A n ) → ((OpMultUnaryAntiDistributionTerm2 n A ) → A ))))
  evalOpE n Mu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mu vars (sing2 x1 )  = x1 
  
  evalOpE n Mu vars (primOL2 x1 )  = ((prim Mu ) (evalOpE n Mu vars x1 ) )
  
  evalOpE n Mu vars (*OL2 x1 x2 )  = ((* Mu ) (evalOpE n Mu vars x1 ) (evalOpE n Mu vars x2 ) )
  
  inductionB : ((P  : (MultUnaryAntiDistributionTerm  → Set ))  → (((x1  : MultUnaryAntiDistributionTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : MultUnaryAntiDistributionTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : MultUnaryAntiDistributionTerm )  → (P x )))))
  inductionB p ppriml p*l (primL x1 )  = (ppriml _ (inductionB p ppriml p*l x1 ) )
  
  inductionB p ppriml p*l (*L x1 x2 )  = (p*l _ _ (inductionB p ppriml p*l x1 ) (inductionB p ppriml p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMultUnaryAntiDistributionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClMultUnaryAntiDistributionTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClMultUnaryAntiDistributionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClMultUnaryAntiDistributionTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl p*cl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl p*cl x1 ) )
  
  inductionCl _ p psing pprimcl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing pprimcl p*cl x1 ) (inductionCl _ p psing pprimcl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMultUnaryAntiDistributionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpMultUnaryAntiDistributionTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpMultUnaryAntiDistributionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpMultUnaryAntiDistributionTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol p*ol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol p*ol x1 ) )
  
  inductionOp _ p pv pprimol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv pprimol p*ol x1 ) (inductionOp _ p pv pprimol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMultUnaryAntiDistributionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpMultUnaryAntiDistributionTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpMultUnaryAntiDistributionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpMultUnaryAntiDistributionTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 x2 ) )
  
  primL' : (  (MultUnaryAntiDistributionTerm   → MultUnaryAntiDistributionTerm  ))
  primL' x1  = (primL x1 )
  
  *L' : (  (MultUnaryAntiDistributionTerm   → (MultUnaryAntiDistributionTerm   → MultUnaryAntiDistributionTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (MultUnaryAntiDistributionTerm  → (Staged MultUnaryAntiDistributionTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClMultUnaryAntiDistributionTerm A )  → (ClMultUnaryAntiDistributionTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  *Cl' : ({A  : Set }  → ((ClMultUnaryAntiDistributionTerm A )  → ((ClMultUnaryAntiDistributionTerm A )  → (ClMultUnaryAntiDistributionTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMultUnaryAntiDistributionTerm A ) → (Staged (ClMultUnaryAntiDistributionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpMultUnaryAntiDistributionTerm n )  → (OpMultUnaryAntiDistributionTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  *OL' : ({n  : Nat}  → ((OpMultUnaryAntiDistributionTerm n )  → ((OpMultUnaryAntiDistributionTerm n )  → (OpMultUnaryAntiDistributionTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMultUnaryAntiDistributionTerm n ) → (Staged (OpMultUnaryAntiDistributionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpMultUnaryAntiDistributionTerm2 n A )  → (OpMultUnaryAntiDistributionTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpMultUnaryAntiDistributionTerm2 n A )  → ((OpMultUnaryAntiDistributionTerm2 n A )  → (OpMultUnaryAntiDistributionTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMultUnaryAntiDistributionTerm2 n A ) → (Staged (OpMultUnaryAntiDistributionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))