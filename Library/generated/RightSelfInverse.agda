
 module RightSelfInverse  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightSelfInverse (A  : Set )  : Set where
    constructor RightSelfInverseC
    field
      |> : (A  → (A  → A ))
      rightSelfInverse_|> : ({x y  : A }  → (|> (|> x y ) y )  ≡ x ) 
  
  open RightSelfInverse
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      |>S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      |>P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      rightSelfInverse_|>P : ({xP yP  : (Prod AP AP )}  → (|>P (|>P xP yP ) yP )  ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Ri1  : (RightSelfInverse A1 )) (Ri2  : (RightSelfInverse A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Ri1 ) x1 x2 ) ) ≡ ((|> Ri2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightSelfInverse A1 )) (Ri2  : (RightSelfInverse A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Ri1 ) x1 x2 ) ((|> Ri2 ) y1 y2 ) )))) 
  
  data RightSelfInverseTerm  : Set where
    |>L : (RightSelfInverseTerm   → (RightSelfInverseTerm   → RightSelfInverseTerm  )) 
  
  data ClRightSelfInverseTerm (A  : Set )  : Set where
    sing : (A  → (ClRightSelfInverseTerm A ) )
    |>Cl : ((ClRightSelfInverseTerm A )  → ((ClRightSelfInverseTerm A )  → (ClRightSelfInverseTerm A ) )) 
  
  data OpRightSelfInverseTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightSelfInverseTerm n ) )
    |>OL : ((OpRightSelfInverseTerm n )  → ((OpRightSelfInverseTerm n )  → (OpRightSelfInverseTerm n ) )) 
  
  data OpRightSelfInverseTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightSelfInverseTerm2 n A ) )
    sing2 : (A  → (OpRightSelfInverseTerm2 n A ) )
    |>OL2 : ((OpRightSelfInverseTerm2 n A )  → ((OpRightSelfInverseTerm2 n A )  → (OpRightSelfInverseTerm2 n A ) )) 
  
  simplifyB : (RightSelfInverseTerm  → RightSelfInverseTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRightSelfInverseTerm A ) → (ClRightSelfInverseTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRightSelfInverseTerm n ) → (OpRightSelfInverseTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRightSelfInverseTerm2 n A ) → (OpRightSelfInverseTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((RightSelfInverse A ) → (RightSelfInverseTerm  → A )))
  evalB Ri (|>L x1 x2 )  = ((|> Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightSelfInverse A ) → ((ClRightSelfInverseTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (|>Cl x1 x2 )  = ((|> Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightSelfInverse A ) → ((Vec A n ) → ((OpRightSelfInverseTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (|>OL x1 x2 )  = ((|> Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightSelfInverse A ) → ((Vec A n ) → ((OpRightSelfInverseTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (|>OL2 x1 x2 )  = ((|> Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightSelfInverseTerm  → Set ))  → (((x1 x2  : RightSelfInverseTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → ((x  : RightSelfInverseTerm )  → (P x ))))
  inductionB p p|>l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l x1 ) (inductionB p p|>l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightSelfInverseTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRightSelfInverseTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → ((x  : (ClRightSelfInverseTerm A ))  → (P x )))))
  inductionCl _ p psing p|>cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl x1 ) (inductionCl _ p psing p|>cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightSelfInverseTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRightSelfInverseTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → ((x  : (OpRightSelfInverseTerm n ))  → (P x )))))
  inductionOp _ p pv p|>ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol x1 ) (inductionOp _ p pv p|>ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightSelfInverseTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRightSelfInverseTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → ((x  : (OpRightSelfInverseTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 x2 ) )
  
  |>L' : (  (RightSelfInverseTerm   → (RightSelfInverseTerm   → RightSelfInverseTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  stageB : (RightSelfInverseTerm  → (Staged RightSelfInverseTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClRightSelfInverseTerm A )  → ((ClRightSelfInverseTerm A )  → (ClRightSelfInverseTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightSelfInverseTerm A ) → (Staged (ClRightSelfInverseTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpRightSelfInverseTerm n )  → ((OpRightSelfInverseTerm n )  → (OpRightSelfInverseTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightSelfInverseTerm n ) → (Staged (OpRightSelfInverseTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpRightSelfInverseTerm2 n A )  → ((OpRightSelfInverseTerm2 n A )  → (OpRightSelfInverseTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightSelfInverseTerm2 n A ) → (Staged (OpRightSelfInverseTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
