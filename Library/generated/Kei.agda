module Kei  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Kei (A  : Set )  : Set where
    constructor KeiC
    field
      |> : (A  → (A  → A ))
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) ))
      idempotent_|> : ({x  : A }  → (|> x x ) ≡ x )
      rightSelfInverse_|> : ({x y  : A }  → (|> (|> x y ) y )  ≡ x )
  open Kei
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      |>S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      |>P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftDistributiveP : ({xP yP zP  : (Prod AP AP )}  → (|>P xP (|>P yP zP ) ) ≡ (|>P (|>P xP yP ) (|>P xP zP ) ))
      idempotent_|>P : ({xP  : (Prod AP AP )}  → (|>P xP xP ) ≡ xP )
      rightSelfInverse_|>P : ({xP yP  : (Prod AP AP )}  → (|>P (|>P xP yP ) yP )  ≡ xP )
  record Hom (A1 A2  : Set ) (Ke1  : (Kei A1 )) (Ke2  : (Kei A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Ke1 ) x1 x2 ) ) ≡ ((|> Ke2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ke1  : (Kei A1 )) (Ke2  : (Kei A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Ke1 ) x1 x2 ) ((|> Ke2 ) y1 y2 ) ))))
  data KeiTerm  : Set where
    |>L : (KeiTerm   → (KeiTerm   → KeiTerm  ))
  data ClKeiTerm (A  : Set )  : Set where
    sing : (A  → (ClKeiTerm A ) )
    |>Cl : ((ClKeiTerm A )  → ((ClKeiTerm A )  → (ClKeiTerm A ) ))
  data OpKeiTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpKeiTerm n ) )
    |>OL : ((OpKeiTerm n )  → ((OpKeiTerm n )  → (OpKeiTerm n ) ))
  data OpKeiTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpKeiTerm2 n A ) )
    sing2 : (A  → (OpKeiTerm2 n A ) )
    |>OL2 : ((OpKeiTerm2 n A )  → ((OpKeiTerm2 n A )  → (OpKeiTerm2 n A ) ))
  evalB : ({A  : Set }  → ((Kei A ) → (KeiTerm  → A )))
  evalB Ke (|>L x1 x2 )  = ((|> Ke ) (evalB Ke x1 ) (evalB Ke x2 ) )
  
  evalCl : ({A  : Set }  → ((Kei A ) → ((ClKeiTerm A ) → A )))
  evalCl Ke (sing x1 )  = x1 
  
  evalCl Ke (|>Cl x1 x2 )  = ((|> Ke ) (evalCl Ke x1 ) (evalCl Ke x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Kei A ) → ((Vec A n ) → ((OpKeiTerm n ) → A ))))
  evalOp n Ke vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ke vars (|>OL x1 x2 )  = ((|> Ke ) (evalOp n Ke vars x1 ) (evalOp n Ke vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Kei A ) → ((Vec A n ) → ((OpKeiTerm2 n A ) → A ))))
  evalOpE n Ke vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ke vars (sing2 x1 )  = x1 
  
  evalOpE n Ke vars (|>OL2 x1 x2 )  = ((|> Ke ) (evalOpE n Ke vars x1 ) (evalOpE n Ke vars x2 ) )
  
  inductionB : ((P  : (KeiTerm  → Set ))  → (((x1 x2  : KeiTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → ((x  : KeiTerm )  → (P x ))))
  inductionB p p|>l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l x1 ) (inductionB p p|>l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClKeiTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClKeiTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → ((x  : (ClKeiTerm A ))  → (P x )))))
  inductionCl _ p psing p|>cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl x1 ) (inductionCl _ p psing p|>cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpKeiTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpKeiTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → ((x  : (OpKeiTerm n ))  → (P x )))))
  inductionOp _ p pv p|>ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol x1 ) (inductionOp _ p pv p|>ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpKeiTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpKeiTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → ((x  : (OpKeiTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 x2 ) )
  
  |>L' : (  (KeiTerm   → (KeiTerm   → KeiTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  stageB : (KeiTerm  → (Staged KeiTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClKeiTerm A )  → ((ClKeiTerm A )  → (ClKeiTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClKeiTerm A ) → (Staged (ClKeiTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpKeiTerm n )  → ((OpKeiTerm n )  → (OpKeiTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpKeiTerm n ) → (Staged (OpKeiTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpKeiTerm2 n A )  → ((OpKeiTerm2 n A )  → (OpKeiTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpKeiTerm2 n A ) → (Staged (OpKeiTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))