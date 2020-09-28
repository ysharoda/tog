module PointedOne  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedOne (A  : Set )  : Set where
    constructor PointedOneC
    field
      1ᵢ : A 
  open PointedOne
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      1S : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      1P : (Prod AP AP )
  record Hom (A1 A2  : Set ) (Po1  : (PointedOne A1 )) (Po2  : (PointedOne A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-1 : (  (hom (1ᵢ Po1 )  ) ≡ (1ᵢ Po2 ) )
  record RelInterp (A1 A2  : Set ) (Po1  : (PointedOne A1 )) (Po2  : (PointedOne A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-1 : (  (interp (1ᵢ Po1 )  (1ᵢ Po2 )  ))
  data PointedOneTerm  : Set where
    1L : PointedOneTerm  
  data ClPointedOneTerm (A  : Set )  : Set where
    sing : (A  → (ClPointedOneTerm A ) )
    1Cl : (ClPointedOneTerm A ) 
  data OpPointedOneTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointedOneTerm n ) )
    1OL : (OpPointedOneTerm n ) 
  data OpPointedOneTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointedOneTerm2 n A ) )
    sing2 : (A  → (OpPointedOneTerm2 n A ) )
    1OL2 : (OpPointedOneTerm2 n A ) 
  evalB : ({A  : Set }  → ((PointedOne A ) → (PointedOneTerm  → A )))
  evalB Po 1L  = (1ᵢ Po ) 
  
  evalCl : ({A  : Set }  → ((PointedOne A ) → ((ClPointedOneTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po 1Cl  = (1ᵢ Po ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PointedOne A ) → ((Vec A n ) → ((OpPointedOneTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars 1OL  = (1ᵢ Po ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PointedOne A ) → ((Vec A n ) → ((OpPointedOneTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars 1OL2  = (1ᵢ Po ) 
  
  inductionB : ((P  : (PointedOneTerm  → Set ))  → ((P 1L ) → ((x  : PointedOneTerm )  → (P x ))))
  inductionB p p1l 1L  = p1l 
  
  inductionCl : ((A  : Set ) (P  : ((ClPointedOneTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 1Cl ) → ((x  : (ClPointedOneTerm A ))  → (P x )))))
  inductionCl _ p psing p1cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p1cl 1Cl  = p1cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpPointedOneTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 1OL ) → ((x  : (OpPointedOneTerm n ))  → (P x )))))
  inductionOp _ p pv p1ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p1ol 1OL  = p1ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointedOneTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 1OL2 ) → ((x  : (OpPointedOneTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p1ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 1OL2  = p1ol2 
  
  1L' : (  PointedOneTerm  )
  1L'  = 1L 
  
  stageB : (PointedOneTerm  → (Staged PointedOneTerm  ))
  stageB 1L  = (Now 1L )
  
  1Cl' : ({A  : Set }  → (ClPointedOneTerm A ) )
  1Cl'  = 1Cl 
  
  stageCl : ((A  : Set )  → ((ClPointedOneTerm A ) → (Staged (ClPointedOneTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  1OL' : ({n  : Nat}  → (OpPointedOneTerm n ) )
  1OL'  = 1OL 
  
  stageOp : ((n  : Nat)  → ((OpPointedOneTerm n ) → (Staged (OpPointedOneTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpPointedOneTerm2 n A ) )
  1OL2'  = 1OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedOneTerm2 n A ) → (Staged (OpPointedOneTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      1T : (Repr A ) 