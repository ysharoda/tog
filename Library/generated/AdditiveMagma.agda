
 module AdditiveMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AdditiveMagma (A  : Set )  : Set where
    constructor AdditiveMagmaC
    field
      + : (A  → (A  → A )) 
  
  open AdditiveMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (Ad1  : (AdditiveMagma A1 )) (Ad2  : (AdditiveMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ad1 ) x1 x2 ) ) ≡ ((+ Ad2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ad1  : (AdditiveMagma A1 )) (Ad2  : (AdditiveMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ad1 ) x1 x2 ) ((+ Ad2 ) y1 y2 ) )))) 
  
  data AdditiveMagmaTerm  : Set where
    +L : (AdditiveMagmaTerm   → (AdditiveMagmaTerm   → AdditiveMagmaTerm  )) 
  
  data ClAdditiveMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClAdditiveMagmaTerm A ) )
    +Cl : ((ClAdditiveMagmaTerm A )  → ((ClAdditiveMagmaTerm A )  → (ClAdditiveMagmaTerm A ) )) 
  
  data OpAdditiveMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAdditiveMagmaTerm n ) )
    +OL : ((OpAdditiveMagmaTerm n )  → ((OpAdditiveMagmaTerm n )  → (OpAdditiveMagmaTerm n ) )) 
  
  data OpAdditiveMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAdditiveMagmaTerm2 n A ) )
    sing2 : (A  → (OpAdditiveMagmaTerm2 n A ) )
    +OL2 : ((OpAdditiveMagmaTerm2 n A )  → ((OpAdditiveMagmaTerm2 n A )  → (OpAdditiveMagmaTerm2 n A ) )) 
  
  simplifyB : (AdditiveMagmaTerm  → AdditiveMagmaTerm )
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAdditiveMagmaTerm A ) → (ClAdditiveMagmaTerm A )))
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAdditiveMagmaTerm n ) → (OpAdditiveMagmaTerm n )))
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveMagmaTerm2 n A ) → (OpAdditiveMagmaTerm2 n A )))
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AdditiveMagma A ) → (AdditiveMagmaTerm  → A )))
  evalB Ad (+L x1 x2 )  = ((+ Ad ) (evalB Ad x1 ) (evalB Ad x2 ) )
  
  evalCl : ({A  : Set }  → ((AdditiveMagma A ) → ((ClAdditiveMagmaTerm A ) → A )))
  evalCl Ad (sing x1 )  = x1 
  
  evalCl Ad (+Cl x1 x2 )  = ((+ Ad ) (evalCl Ad x1 ) (evalCl Ad x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AdditiveMagma A ) → ((Vec A n ) → ((OpAdditiveMagmaTerm n ) → A ))))
  evalOp n Ad vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ad vars (+OL x1 x2 )  = ((+ Ad ) (evalOp n Ad vars x1 ) (evalOp n Ad vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AdditiveMagma A ) → ((Vec A n ) → ((OpAdditiveMagmaTerm2 n A ) → A ))))
  evalOpE n Ad vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ad vars (sing2 x1 )  = x1 
  
  evalOpE n Ad vars (+OL2 x1 x2 )  = ((+ Ad ) (evalOpE n Ad vars x1 ) (evalOpE n Ad vars x2 ) )
  
  inductionB : ((P  : (AdditiveMagmaTerm  → Set ))  → (((x1 x2  : AdditiveMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : AdditiveMagmaTerm )  → (P x ))))
  inductionB p p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l x1 ) (inductionB p p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAdditiveMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAdditiveMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClAdditiveMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl x1 ) (inductionCl _ p psing p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAdditiveMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAdditiveMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpAdditiveMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol x1 ) (inductionOp _ p pv p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAdditiveMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAdditiveMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpAdditiveMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 x2 ) )
  
  +L' : (  (AdditiveMagmaTerm   → (AdditiveMagmaTerm   → AdditiveMagmaTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (AdditiveMagmaTerm  → (Staged AdditiveMagmaTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClAdditiveMagmaTerm A )  → ((ClAdditiveMagmaTerm A )  → (ClAdditiveMagmaTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAdditiveMagmaTerm A ) → (Staged (ClAdditiveMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpAdditiveMagmaTerm n )  → ((OpAdditiveMagmaTerm n )  → (OpAdditiveMagmaTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAdditiveMagmaTerm n ) → (Staged (OpAdditiveMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpAdditiveMagmaTerm2 n A )  → ((OpAdditiveMagmaTerm2 n A )  → (OpAdditiveMagmaTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAdditiveMagmaTerm2 n A ) → (Staged (OpAdditiveMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
