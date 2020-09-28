module Rack  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Rack (A  : Set )  : Set where
    constructor RackC
    field
      |> : (A  → (A  → A ))
      <| : (A  → (A  → A ))
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) ))
      rightDistributive : ({x y z  : A }  → (<| (<| y z ) x ) ≡ (<| (<| y x ) (<| z x ) ))
      leftInverse : ({x y  : A }  → (<| (|> x y ) x ) ≡ y )
      rightInverse : ({x y  : A }  → (|> x (<| y x ) ) ≡ y )
  open Rack
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      |>S : (AS  → (AS  → AS ))
      <|S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      |>P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      <|P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftDistributiveP : ({xP yP zP  : (Prod AP AP )}  → (|>P xP (|>P yP zP ) ) ≡ (|>P (|>P xP yP ) (|>P xP zP ) ))
      rightDistributiveP : ({xP yP zP  : (Prod AP AP )}  → (<|P (<|P yP zP ) xP ) ≡ (<|P (<|P yP xP ) (<|P zP xP ) ))
      leftInverseP : ({xP yP  : (Prod AP AP )}  → (<|P (|>P xP yP ) xP ) ≡ yP )
      rightInverseP : ({xP yP  : (Prod AP AP )}  → (|>P xP (<|P yP xP ) ) ≡ yP )
  record Hom (A1 A2  : Set ) (Ra1  : (Rack A1 )) (Ra2  : (Rack A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Ra1 ) x1 x2 ) ) ≡ ((|> Ra2 ) (hom x1 ) (hom x2 ) ))
      pres-<| : ({x1  : A1} {x2  : A1}  → (hom ((<| Ra1 ) x1 x2 ) ) ≡ ((<| Ra2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ra1  : (Rack A1 )) (Ra2  : (Rack A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Ra1 ) x1 x2 ) ((|> Ra2 ) y1 y2 ) ))))
      interp-<| : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((<| Ra1 ) x1 x2 ) ((<| Ra2 ) y1 y2 ) ))))
  data RackTerm  : Set where
    |>L : (RackTerm   → (RackTerm   → RackTerm  ))
    <|L : (RackTerm   → (RackTerm   → RackTerm  ))
  data ClRackTerm (A  : Set )  : Set where
    sing : (A  → (ClRackTerm A ) )
    |>Cl : ((ClRackTerm A )  → ((ClRackTerm A )  → (ClRackTerm A ) ))
    <|Cl : ((ClRackTerm A )  → ((ClRackTerm A )  → (ClRackTerm A ) ))
  data OpRackTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRackTerm n ) )
    |>OL : ((OpRackTerm n )  → ((OpRackTerm n )  → (OpRackTerm n ) ))
    <|OL : ((OpRackTerm n )  → ((OpRackTerm n )  → (OpRackTerm n ) ))
  data OpRackTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRackTerm2 n A ) )
    sing2 : (A  → (OpRackTerm2 n A ) )
    |>OL2 : ((OpRackTerm2 n A )  → ((OpRackTerm2 n A )  → (OpRackTerm2 n A ) ))
    <|OL2 : ((OpRackTerm2 n A )  → ((OpRackTerm2 n A )  → (OpRackTerm2 n A ) ))
  evalB : ({A  : Set }  → ((Rack A ) → (RackTerm  → A )))
  evalB Ra (|>L x1 x2 )  = ((|> Ra ) (evalB Ra x1 ) (evalB Ra x2 ) )
  
  evalB Ra (<|L x1 x2 )  = ((<| Ra ) (evalB Ra x1 ) (evalB Ra x2 ) )
  
  evalCl : ({A  : Set }  → ((Rack A ) → ((ClRackTerm A ) → A )))
  evalCl Ra (sing x1 )  = x1 
  
  evalCl Ra (|>Cl x1 x2 )  = ((|> Ra ) (evalCl Ra x1 ) (evalCl Ra x2 ) )
  
  evalCl Ra (<|Cl x1 x2 )  = ((<| Ra ) (evalCl Ra x1 ) (evalCl Ra x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Rack A ) → ((Vec A n ) → ((OpRackTerm n ) → A ))))
  evalOp n Ra vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ra vars (|>OL x1 x2 )  = ((|> Ra ) (evalOp n Ra vars x1 ) (evalOp n Ra vars x2 ) )
  
  evalOp n Ra vars (<|OL x1 x2 )  = ((<| Ra ) (evalOp n Ra vars x1 ) (evalOp n Ra vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Rack A ) → ((Vec A n ) → ((OpRackTerm2 n A ) → A ))))
  evalOpE n Ra vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ra vars (sing2 x1 )  = x1 
  
  evalOpE n Ra vars (|>OL2 x1 x2 )  = ((|> Ra ) (evalOpE n Ra vars x1 ) (evalOpE n Ra vars x2 ) )
  
  evalOpE n Ra vars (<|OL2 x1 x2 )  = ((<| Ra ) (evalOpE n Ra vars x1 ) (evalOpE n Ra vars x2 ) )
  
  inductionB : ((P  : (RackTerm  → Set ))  → (((x1 x2  : RackTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → (((x1 x2  : RackTerm  )  → ((P x1 ) → ((P x2 ) → (P (<|L x1 x2 ) )))) → ((x  : RackTerm )  → (P x )))))
  inductionB p p|>l p<|l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionB p p|>l p<|l (<|L x1 x2 )  = (p<|l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRackTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRackTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → (((x1 x2  : (ClRackTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (<|Cl x1 x2 ) )))) → ((x  : (ClRackTerm A ))  → (P x ))))))
  inductionCl _ p psing p|>cl p<|cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2 )  = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRackTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRackTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → (((x1 x2  : (OpRackTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL x1 x2 ) )))) → ((x  : (OpRackTerm n ))  → (P x ))))))
  inductionOp _ p pv p|>ol p<|ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol p<|ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOp _ p pv p|>ol p<|ol (<|OL x1 x2 )  = (p<|ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRackTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRackTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → (((x1 x2  : (OpRackTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL2 x1 x2 ) )))) → ((x  : (OpRackTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2 )  = (p<|ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  |>L' : (  (RackTerm   → (RackTerm   → RackTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  <|L' : (  (RackTerm   → (RackTerm   → RackTerm  )))
  <|L' x1 x2  = (<|L x1 x2 )
  
  stageB : (RackTerm  → (Staged RackTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (<|L x1 x2 )  = (stage2 <|L' (codeLift2 <|L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClRackTerm A )  → ((ClRackTerm A )  → (ClRackTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  <|Cl' : ({A  : Set }  → ((ClRackTerm A )  → ((ClRackTerm A )  → (ClRackTerm A ) )))
  <|Cl' x1 x2  = (<|Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRackTerm A ) → (Staged (ClRackTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (<|Cl x1 x2 )  = (stage2 <|Cl' (codeLift2 <|Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpRackTerm n )  → ((OpRackTerm n )  → (OpRackTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  <|OL' : ({n  : Nat}  → ((OpRackTerm n )  → ((OpRackTerm n )  → (OpRackTerm n ) )))
  <|OL' x1 x2  = (<|OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRackTerm n ) → (Staged (OpRackTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (<|OL x1 x2 )  = (stage2 <|OL' (codeLift2 <|OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpRackTerm2 n A )  → ((OpRackTerm2 n A )  → (OpRackTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  <|OL2' : ({n  : Nat } {A  : Set }  → ((OpRackTerm2 n A )  → ((OpRackTerm2 n A )  → (OpRackTerm2 n A ) )))
  <|OL2' x1 x2  = (<|OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRackTerm2 n A ) → (Staged (OpRackTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (<|OL2 x1 x2 )  = (stage2 <|OL2' (codeLift2 <|OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      <|T : ((Repr A )  → ((Repr A )  → (Repr A ) ))