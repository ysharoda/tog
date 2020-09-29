
 module PointedZero  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedZero (A  : Set )  : Set where
    constructor PointedZeroC
    field
      0ᵢ : A  
  
  open PointedZero
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP ) 
  
  record Hom (A1 A2  : Set ) (Po1  : (PointedZero A1 )) (Po2  : (PointedZero A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Po1 )  ) ≡ (0ᵢ Po2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Po1  : (PointedZero A1 )) (Po2  : (PointedZero A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Po1 )  (0ᵢ Po2 )  )) 
  
  data PointedZeroTerm  : Set where
    0L : PointedZeroTerm   
  
  data ClPointedZeroTerm (A  : Set )  : Set where
    sing : (A  → (ClPointedZeroTerm A ) )
    0Cl : (ClPointedZeroTerm A )  
  
  data OpPointedZeroTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointedZeroTerm n ) )
    0OL : (OpPointedZeroTerm n )  
  
  data OpPointedZeroTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointedZeroTerm2 n A ) )
    sing2 : (A  → (OpPointedZeroTerm2 n A ) )
    0OL2 : (OpPointedZeroTerm2 n A )  
  
  simplifyB : (PointedZeroTerm  → PointedZeroTerm )
  simplifyB 0L  = 0L 
  
  simplifyCl : ((A  : Set )  → ((ClPointedZeroTerm A ) → (ClPointedZeroTerm A )))
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPointedZeroTerm n ) → (OpPointedZeroTerm n )))
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedZeroTerm2 n A ) → (OpPointedZeroTerm2 n A )))
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PointedZero A ) → (PointedZeroTerm  → A )))
  evalB Po 0L  = (0ᵢ Po ) 
  
  evalCl : ({A  : Set }  → ((PointedZero A ) → ((ClPointedZeroTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po 0Cl  = (0ᵢ Po ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PointedZero A ) → ((Vec A n ) → ((OpPointedZeroTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars 0OL  = (0ᵢ Po ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PointedZero A ) → ((Vec A n ) → ((OpPointedZeroTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars 0OL2  = (0ᵢ Po ) 
  
  inductionB : ((P  : (PointedZeroTerm  → Set ))  → ((P 0L ) → ((x  : PointedZeroTerm )  → (P x ))))
  inductionB p p0l 0L  = p0l 
  
  inductionCl : ((A  : Set ) (P  : ((ClPointedZeroTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → ((x  : (ClPointedZeroTerm A ))  → (P x )))))
  inductionCl _ p psing p0cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl 0Cl  = p0cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpPointedZeroTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → ((x  : (OpPointedZeroTerm n ))  → (P x )))))
  inductionOp _ p pv p0ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol 0OL  = p0ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointedZeroTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → ((x  : (OpPointedZeroTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 0OL2  = p0ol2 
  
  0L' : (  PointedZeroTerm  )
  0L'  = 0L 
  
  stageB : (PointedZeroTerm  → (Staged PointedZeroTerm  ))
  stageB 0L  = (Now 0L )
  
  0Cl' : ({A  : Set }  → (ClPointedZeroTerm A ) )
  0Cl'  = 0Cl 
  
  stageCl : ((A  : Set )  → ((ClPointedZeroTerm A ) → (Staged (ClPointedZeroTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  0OL' : ({n  : Nat}  → (OpPointedZeroTerm n ) )
  0OL'  = 0OL 
  
  stageOp : ((n  : Nat)  → ((OpPointedZeroTerm n ) → (Staged (OpPointedZeroTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpPointedZeroTerm2 n A ) )
  0OL2'  = 0OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedZeroTerm2 n A ) → (Staged (OpPointedZeroTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A )  
   
