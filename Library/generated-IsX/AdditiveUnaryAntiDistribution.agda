
 module AdditiveUnaryAntiDistribution  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAdditiveUnaryAntiDistribution (A  : Set ) (prim  : (A  → A )) (+  : (A  → (A  → A )))  : Set where
    constructor IsAdditiveUnaryAntiDistributionC
    field
      antidis_prim_+ : ({x y  : A }  → (prim (+ x y ) ) ≡ (+ (prim y ) (prim x ) )) 
  
  record AdditiveUnaryAntiDistribution (A  : Set )  : Set where
    constructor AdditiveUnaryAntiDistributionC
    field
      prim : (A  → A )
      + : (A  → (A  → A ))
      isAdditiveUnaryAntiDistribution : (IsAdditiveUnaryAntiDistribution A prim (+) ) 
  
  open AdditiveUnaryAntiDistribution
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      antidis_prim_+P : ({xP yP  : (Prod AP AP )}  → (primP (+P xP yP ) ) ≡ (+P (primP yP ) (primP xP ) )) 
  
  record Hom (A1 A2  : Set ) (Ad1  : (AdditiveUnaryAntiDistribution A1 )) (Ad2  : (AdditiveUnaryAntiDistribution A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Ad1 ) x1 ) ) ≡ ((prim Ad2 ) (hom x1 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ad1 ) x1 x2 ) ) ≡ ((+ Ad2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ad1  : (AdditiveUnaryAntiDistribution A1 )) (Ad2  : (AdditiveUnaryAntiDistribution A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Ad1 ) x1 ) ((prim Ad2 ) y1 ) )))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ad1 ) x1 x2 ) ((+ Ad2 ) y1 y2 ) )))) 
  
  data AdditiveUnaryAntiDistributionTerm  : Set where
    primL : (AdditiveUnaryAntiDistributionTerm   → AdditiveUnaryAntiDistributionTerm  )
    +L : (AdditiveUnaryAntiDistributionTerm   → (AdditiveUnaryAntiDistributionTerm   → AdditiveUnaryAntiDistributionTerm  )) 
  
  data ClAdditiveUnaryAntiDistributionTerm (A  : Set )  : Set where
    sing : (A  → (ClAdditiveUnaryAntiDistributionTerm A ) )
    primCl : ((ClAdditiveUnaryAntiDistributionTerm A )  → (ClAdditiveUnaryAntiDistributionTerm A ) )
    +Cl : ((ClAdditiveUnaryAntiDistributionTerm A )  → ((ClAdditiveUnaryAntiDistributionTerm A )  → (ClAdditiveUnaryAntiDistributionTerm A ) )) 
  
  data OpAdditiveUnaryAntiDistributionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAdditiveUnaryAntiDistributionTerm n ) )
    primOL : ((OpAdditiveUnaryAntiDistributionTerm n )  → (OpAdditiveUnaryAntiDistributionTerm n ) )
    +OL : ((OpAdditiveUnaryAntiDistributionTerm n )  → ((OpAdditiveUnaryAntiDistributionTerm n )  → (OpAdditiveUnaryAntiDistributionTerm n ) )) 
  
  data OpAdditiveUnaryAntiDistributionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAdditiveUnaryAntiDistributionTerm2 n A ) )
    sing2 : (A  → (OpAdditiveUnaryAntiDistributionTerm2 n A ) )
    primOL2 : ((OpAdditiveUnaryAntiDistributionTerm2 n A )  → (OpAdditiveUnaryAntiDistributionTerm2 n A ) )
    +OL2 : ((OpAdditiveUnaryAntiDistributionTerm2 n A )  → ((OpAdditiveUnaryAntiDistributionTerm2 n A )  → (OpAdditiveUnaryAntiDistributionTerm2 n A ) )) 
  
  simplifyB : (AdditiveUnaryAntiDistributionTerm  → AdditiveUnaryAntiDistributionTerm )
  simplifyB (+L (primL y ) (primL x ) )  = (primL (+L x y ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAdditiveUnaryAntiDistributionTerm A ) → (ClAdditiveUnaryAntiDistributionTerm A )))
  simplifyCl _ (+Cl (primCl y ) (primCl x ) )  = (primCl (+Cl x y ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAdditiveUnaryAntiDistributionTerm n ) → (OpAdditiveUnaryAntiDistributionTerm n )))
  simplifyOp _ (+OL (primOL y ) (primOL x ) )  = (primOL (+OL x y ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveUnaryAntiDistributionTerm2 n A ) → (OpAdditiveUnaryAntiDistributionTerm2 n A )))
  simplifyOpE _ _ (+OL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (+OL2 x y ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AdditiveUnaryAntiDistribution A ) → (AdditiveUnaryAntiDistributionTerm  → A )))
  evalB Ad (primL x1 )  = ((prim Ad ) (evalB Ad x1 ) )
  
  evalB Ad (+L x1 x2 )  = ((+ Ad ) (evalB Ad x1 ) (evalB Ad x2 ) )
  
  evalCl : ({A  : Set }  → ((AdditiveUnaryAntiDistribution A ) → ((ClAdditiveUnaryAntiDistributionTerm A ) → A )))
  evalCl Ad (sing x1 )  = x1 
  
  evalCl Ad (primCl x1 )  = ((prim Ad ) (evalCl Ad x1 ) )
  
  evalCl Ad (+Cl x1 x2 )  = ((+ Ad ) (evalCl Ad x1 ) (evalCl Ad x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AdditiveUnaryAntiDistribution A ) → ((Vec A n ) → ((OpAdditiveUnaryAntiDistributionTerm n ) → A ))))
  evalOp n Ad vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ad vars (primOL x1 )  = ((prim Ad ) (evalOp n Ad vars x1 ) )
  
  evalOp n Ad vars (+OL x1 x2 )  = ((+ Ad ) (evalOp n Ad vars x1 ) (evalOp n Ad vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AdditiveUnaryAntiDistribution A ) → ((Vec A n ) → ((OpAdditiveUnaryAntiDistributionTerm2 n A ) → A ))))
  evalOpE n Ad vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ad vars (sing2 x1 )  = x1 
  
  evalOpE n Ad vars (primOL2 x1 )  = ((prim Ad ) (evalOpE n Ad vars x1 ) )
  
  evalOpE n Ad vars (+OL2 x1 x2 )  = ((+ Ad ) (evalOpE n Ad vars x1 ) (evalOpE n Ad vars x2 ) )
  
  inductionB : ((P  : (AdditiveUnaryAntiDistributionTerm  → Set ))  → (((x1  : AdditiveUnaryAntiDistributionTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : AdditiveUnaryAntiDistributionTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : AdditiveUnaryAntiDistributionTerm )  → (P x )))))
  inductionB p ppriml p+l (primL x1 )  = (ppriml _ (inductionB p ppriml p+l x1 ) )
  
  inductionB p ppriml p+l (+L x1 x2 )  = (p+l _ _ (inductionB p ppriml p+l x1 ) (inductionB p ppriml p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAdditiveUnaryAntiDistributionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClAdditiveUnaryAntiDistributionTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClAdditiveUnaryAntiDistributionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClAdditiveUnaryAntiDistributionTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl p+cl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl p+cl x1 ) )
  
  inductionCl _ p psing pprimcl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing pprimcl p+cl x1 ) (inductionCl _ p psing pprimcl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAdditiveUnaryAntiDistributionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpAdditiveUnaryAntiDistributionTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpAdditiveUnaryAntiDistributionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpAdditiveUnaryAntiDistributionTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol p+ol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol p+ol x1 ) )
  
  inductionOp _ p pv pprimol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv pprimol p+ol x1 ) (inductionOp _ p pv pprimol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAdditiveUnaryAntiDistributionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpAdditiveUnaryAntiDistributionTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpAdditiveUnaryAntiDistributionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpAdditiveUnaryAntiDistributionTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 p+ol2 x2 ) )
  
  primL' : (  (AdditiveUnaryAntiDistributionTerm   → AdditiveUnaryAntiDistributionTerm  ))
  primL' x1  = (primL x1 )
  
  +L' : (  (AdditiveUnaryAntiDistributionTerm   → (AdditiveUnaryAntiDistributionTerm   → AdditiveUnaryAntiDistributionTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (AdditiveUnaryAntiDistributionTerm  → (Staged AdditiveUnaryAntiDistributionTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClAdditiveUnaryAntiDistributionTerm A )  → (ClAdditiveUnaryAntiDistributionTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  +Cl' : ({A  : Set }  → ((ClAdditiveUnaryAntiDistributionTerm A )  → ((ClAdditiveUnaryAntiDistributionTerm A )  → (ClAdditiveUnaryAntiDistributionTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAdditiveUnaryAntiDistributionTerm A ) → (Staged (ClAdditiveUnaryAntiDistributionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpAdditiveUnaryAntiDistributionTerm n )  → (OpAdditiveUnaryAntiDistributionTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  +OL' : ({n  : Nat}  → ((OpAdditiveUnaryAntiDistributionTerm n )  → ((OpAdditiveUnaryAntiDistributionTerm n )  → (OpAdditiveUnaryAntiDistributionTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAdditiveUnaryAntiDistributionTerm n ) → (Staged (OpAdditiveUnaryAntiDistributionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveUnaryAntiDistributionTerm2 n A )  → (OpAdditiveUnaryAntiDistributionTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveUnaryAntiDistributionTerm2 n A )  → ((OpAdditiveUnaryAntiDistributionTerm2 n A )  → (OpAdditiveUnaryAntiDistributionTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveUnaryAntiDistributionTerm2 n A ) → (Staged (OpAdditiveUnaryAntiDistributionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
