
 module LeftShelf  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftShelf (A  : Set ) (|>  : (A  → (A  → A )))  : Set where
    constructor IsLeftShelfC
    field
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) )) 
  
  record LeftShelf (A  : Set )  : Set where
    constructor LeftShelfC
    field
      |> : (A  → (A  → A ))
      isLeftShelf : (IsLeftShelf A |> ) 
  
  open LeftShelf
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      |>S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      |>P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftDistributiveP : ({xP yP zP  : (Prod AP AP )}  → (|>P xP (|>P yP zP ) ) ≡ (|>P (|>P xP yP ) (|>P xP zP ) )) 
  
  record Hom (A1 A2  : Set ) (Le1  : (LeftShelf A1 )) (Le2  : (LeftShelf A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Le1 ) x1 x2 ) ) ≡ ((|> Le2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftShelf A1 )) (Le2  : (LeftShelf A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Le1 ) x1 x2 ) ((|> Le2 ) y1 y2 ) )))) 
  
  data LeftShelfTerm  : Set where
    |>L : (LeftShelfTerm   → (LeftShelfTerm   → LeftShelfTerm  )) 
  
  data ClLeftShelfTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftShelfTerm A ) )
    |>Cl : ((ClLeftShelfTerm A )  → ((ClLeftShelfTerm A )  → (ClLeftShelfTerm A ) )) 
  
  data OpLeftShelfTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftShelfTerm n ) )
    |>OL : ((OpLeftShelfTerm n )  → ((OpLeftShelfTerm n )  → (OpLeftShelfTerm n ) )) 
  
  data OpLeftShelfTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftShelfTerm2 n A ) )
    sing2 : (A  → (OpLeftShelfTerm2 n A ) )
    |>OL2 : ((OpLeftShelfTerm2 n A )  → ((OpLeftShelfTerm2 n A )  → (OpLeftShelfTerm2 n A ) )) 
  
  simplifyB : (LeftShelfTerm  → LeftShelfTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClLeftShelfTerm A ) → (ClLeftShelfTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpLeftShelfTerm n ) → (OpLeftShelfTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftShelfTerm2 n A ) → (OpLeftShelfTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((LeftShelf A ) → (LeftShelfTerm  → A )))
  evalB Le (|>L x1 x2 )  = ((|> Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftShelf A ) → ((ClLeftShelfTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (|>Cl x1 x2 )  = ((|> Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftShelf A ) → ((Vec A n ) → ((OpLeftShelfTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (|>OL x1 x2 )  = ((|> Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftShelf A ) → ((Vec A n ) → ((OpLeftShelfTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (|>OL2 x1 x2 )  = ((|> Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftShelfTerm  → Set ))  → (((x1 x2  : LeftShelfTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → ((x  : LeftShelfTerm )  → (P x ))))
  inductionB p p|>l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l x1 ) (inductionB p p|>l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftShelfTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftShelfTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → ((x  : (ClLeftShelfTerm A ))  → (P x )))))
  inductionCl _ p psing p|>cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl x1 ) (inductionCl _ p psing p|>cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftShelfTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftShelfTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → ((x  : (OpLeftShelfTerm n ))  → (P x )))))
  inductionOp _ p pv p|>ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol x1 ) (inductionOp _ p pv p|>ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftShelfTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftShelfTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → ((x  : (OpLeftShelfTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 x2 ) )
  
  |>L' : (  (LeftShelfTerm   → (LeftShelfTerm   → LeftShelfTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  stageB : (LeftShelfTerm  → (Staged LeftShelfTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClLeftShelfTerm A )  → ((ClLeftShelfTerm A )  → (ClLeftShelfTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftShelfTerm A ) → (Staged (ClLeftShelfTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpLeftShelfTerm n )  → ((OpLeftShelfTerm n )  → (OpLeftShelfTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftShelfTerm n ) → (Staged (OpLeftShelfTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpLeftShelfTerm2 n A )  → ((OpLeftShelfTerm2 n A )  → (OpLeftShelfTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftShelfTerm2 n A ) → (Staged (OpLeftShelfTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
