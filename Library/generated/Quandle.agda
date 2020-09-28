module Quandle  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Quandle (A  : Set )  : Set where
    constructor QuandleC
    field
      |> : (A  → (A  → A ))
      <| : (A  → (A  → A ))
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) ))
      rightDistributive : ({x y z  : A }  → (<| (<| y z ) x ) ≡ (<| (<| y x ) (<| z x ) ))
      leftInverse : ({x y  : A }  → (<| (|> x y ) x ) ≡ y )
      rightInverse : ({x y  : A }  → (|> x (<| y x ) ) ≡ y )
      idempotent_|> : ({x  : A }  → (|> x x ) ≡ x )
      idempotent_<| : ({x  : A }  → (<| x x ) ≡ x )
  open Quandle
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
      idempotent_|>P : ({xP  : (Prod AP AP )}  → (|>P xP xP ) ≡ xP )
      idempotent_<|P : ({xP  : (Prod AP AP )}  → (<|P xP xP ) ≡ xP )
  record Hom (A1 A2  : Set ) (Qu1  : (Quandle A1 )) (Qu2  : (Quandle A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Qu1 ) x1 x2 ) ) ≡ ((|> Qu2 ) (hom x1 ) (hom x2 ) ))
      pres-<| : ({x1  : A1} {x2  : A1}  → (hom ((<| Qu1 ) x1 x2 ) ) ≡ ((<| Qu2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Qu1  : (Quandle A1 )) (Qu2  : (Quandle A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Qu1 ) x1 x2 ) ((|> Qu2 ) y1 y2 ) ))))
      interp-<| : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((<| Qu1 ) x1 x2 ) ((<| Qu2 ) y1 y2 ) ))))
  data QuandleTerm  : Set where
    |>L : (QuandleTerm   → (QuandleTerm   → QuandleTerm  ))
    <|L : (QuandleTerm   → (QuandleTerm   → QuandleTerm  ))
  data ClQuandleTerm (A  : Set )  : Set where
    sing : (A  → (ClQuandleTerm A ) )
    |>Cl : ((ClQuandleTerm A )  → ((ClQuandleTerm A )  → (ClQuandleTerm A ) ))
    <|Cl : ((ClQuandleTerm A )  → ((ClQuandleTerm A )  → (ClQuandleTerm A ) ))
  data OpQuandleTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpQuandleTerm n ) )
    |>OL : ((OpQuandleTerm n )  → ((OpQuandleTerm n )  → (OpQuandleTerm n ) ))
    <|OL : ((OpQuandleTerm n )  → ((OpQuandleTerm n )  → (OpQuandleTerm n ) ))
  data OpQuandleTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpQuandleTerm2 n A ) )
    sing2 : (A  → (OpQuandleTerm2 n A ) )
    |>OL2 : ((OpQuandleTerm2 n A )  → ((OpQuandleTerm2 n A )  → (OpQuandleTerm2 n A ) ))
    <|OL2 : ((OpQuandleTerm2 n A )  → ((OpQuandleTerm2 n A )  → (OpQuandleTerm2 n A ) ))
  evalB : ({A  : Set }  → ((Quandle A ) → (QuandleTerm  → A )))
  evalB Qu (|>L x1 x2 )  = ((|> Qu ) (evalB Qu x1 ) (evalB Qu x2 ) )
  
  evalB Qu (<|L x1 x2 )  = ((<| Qu ) (evalB Qu x1 ) (evalB Qu x2 ) )
  
  evalCl : ({A  : Set }  → ((Quandle A ) → ((ClQuandleTerm A ) → A )))
  evalCl Qu (sing x1 )  = x1 
  
  evalCl Qu (|>Cl x1 x2 )  = ((|> Qu ) (evalCl Qu x1 ) (evalCl Qu x2 ) )
  
  evalCl Qu (<|Cl x1 x2 )  = ((<| Qu ) (evalCl Qu x1 ) (evalCl Qu x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Quandle A ) → ((Vec A n ) → ((OpQuandleTerm n ) → A ))))
  evalOp n Qu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Qu vars (|>OL x1 x2 )  = ((|> Qu ) (evalOp n Qu vars x1 ) (evalOp n Qu vars x2 ) )
  
  evalOp n Qu vars (<|OL x1 x2 )  = ((<| Qu ) (evalOp n Qu vars x1 ) (evalOp n Qu vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Quandle A ) → ((Vec A n ) → ((OpQuandleTerm2 n A ) → A ))))
  evalOpE n Qu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Qu vars (sing2 x1 )  = x1 
  
  evalOpE n Qu vars (|>OL2 x1 x2 )  = ((|> Qu ) (evalOpE n Qu vars x1 ) (evalOpE n Qu vars x2 ) )
  
  evalOpE n Qu vars (<|OL2 x1 x2 )  = ((<| Qu ) (evalOpE n Qu vars x1 ) (evalOpE n Qu vars x2 ) )
  
  inductionB : ((P  : (QuandleTerm  → Set ))  → (((x1 x2  : QuandleTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → (((x1 x2  : QuandleTerm  )  → ((P x1 ) → ((P x2 ) → (P (<|L x1 x2 ) )))) → ((x  : QuandleTerm )  → (P x )))))
  inductionB p p|>l p<|l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionB p p|>l p<|l (<|L x1 x2 )  = (p<|l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClQuandleTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClQuandleTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → (((x1 x2  : (ClQuandleTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (<|Cl x1 x2 ) )))) → ((x  : (ClQuandleTerm A ))  → (P x ))))))
  inductionCl _ p psing p|>cl p<|cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2 )  = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpQuandleTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpQuandleTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → (((x1 x2  : (OpQuandleTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL x1 x2 ) )))) → ((x  : (OpQuandleTerm n ))  → (P x ))))))
  inductionOp _ p pv p|>ol p<|ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol p<|ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOp _ p pv p|>ol p<|ol (<|OL x1 x2 )  = (p<|ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpQuandleTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpQuandleTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → (((x1 x2  : (OpQuandleTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL2 x1 x2 ) )))) → ((x  : (OpQuandleTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2 )  = (p<|ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  |>L' : (  (QuandleTerm   → (QuandleTerm   → QuandleTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  <|L' : (  (QuandleTerm   → (QuandleTerm   → QuandleTerm  )))
  <|L' x1 x2  = (<|L x1 x2 )
  
  stageB : (QuandleTerm  → (Staged QuandleTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (<|L x1 x2 )  = (stage2 <|L' (codeLift2 <|L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClQuandleTerm A )  → ((ClQuandleTerm A )  → (ClQuandleTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  <|Cl' : ({A  : Set }  → ((ClQuandleTerm A )  → ((ClQuandleTerm A )  → (ClQuandleTerm A ) )))
  <|Cl' x1 x2  = (<|Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClQuandleTerm A ) → (Staged (ClQuandleTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (<|Cl x1 x2 )  = (stage2 <|Cl' (codeLift2 <|Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpQuandleTerm n )  → ((OpQuandleTerm n )  → (OpQuandleTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  <|OL' : ({n  : Nat}  → ((OpQuandleTerm n )  → ((OpQuandleTerm n )  → (OpQuandleTerm n ) )))
  <|OL' x1 x2  = (<|OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpQuandleTerm n ) → (Staged (OpQuandleTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (<|OL x1 x2 )  = (stage2 <|OL' (codeLift2 <|OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpQuandleTerm2 n A )  → ((OpQuandleTerm2 n A )  → (OpQuandleTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  <|OL2' : ({n  : Nat } {A  : Set }  → ((OpQuandleTerm2 n A )  → ((OpQuandleTerm2 n A )  → (OpQuandleTerm2 n A ) )))
  <|OL2' x1 x2  = (<|OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpQuandleTerm2 n A ) → (Staged (OpQuandleTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (<|OL2 x1 x2 )  = (stage2 <|OL2' (codeLift2 <|OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      <|T : ((Repr A )  → ((Repr A )  → (Repr A ) ))