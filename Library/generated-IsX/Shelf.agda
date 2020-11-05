
 module Shelf  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsShelf (A  : Set ) (|>  : (A  → (A  → A ))) (<|  : (A  → (A  → A )))  : Set where
    constructor IsShelfC
    field
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) ))
      rightDistributive : ({x y z  : A }  → (<| (<| y z ) x ) ≡ (<| (<| y x ) (<| z x ) )) 
  
  record Shelf (A  : Set )  : Set where
    constructor ShelfC
    field
      |> : (A  → (A  → A ))
      <| : (A  → (A  → A ))
      isShelf : (IsShelf A |> <| ) 
  
  open Shelf
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
  
  record Hom (A1 A2  : Set ) (Sh1  : (Shelf A1 )) (Sh2  : (Shelf A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Sh1 ) x1 x2 ) ) ≡ ((|> Sh2 ) (hom x1 ) (hom x2 ) ))
      pres-<| : ({x1  : A1} {x2  : A1}  → (hom ((<| Sh1 ) x1 x2 ) ) ≡ ((<| Sh2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Sh1  : (Shelf A1 )) (Sh2  : (Shelf A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Sh1 ) x1 x2 ) ((|> Sh2 ) y1 y2 ) ))))
      interp-<| : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((<| Sh1 ) x1 x2 ) ((<| Sh2 ) y1 y2 ) )))) 
  
  data ShelfTerm  : Set where
    |>L : (ShelfTerm   → (ShelfTerm   → ShelfTerm  ))
    <|L : (ShelfTerm   → (ShelfTerm   → ShelfTerm  )) 
  
  data ClShelfTerm (A  : Set )  : Set where
    sing : (A  → (ClShelfTerm A ) )
    |>Cl : ((ClShelfTerm A )  → ((ClShelfTerm A )  → (ClShelfTerm A ) ))
    <|Cl : ((ClShelfTerm A )  → ((ClShelfTerm A )  → (ClShelfTerm A ) )) 
  
  data OpShelfTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpShelfTerm n ) )
    |>OL : ((OpShelfTerm n )  → ((OpShelfTerm n )  → (OpShelfTerm n ) ))
    <|OL : ((OpShelfTerm n )  → ((OpShelfTerm n )  → (OpShelfTerm n ) )) 
  
  data OpShelfTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpShelfTerm2 n A ) )
    sing2 : (A  → (OpShelfTerm2 n A ) )
    |>OL2 : ((OpShelfTerm2 n A )  → ((OpShelfTerm2 n A )  → (OpShelfTerm2 n A ) ))
    <|OL2 : ((OpShelfTerm2 n A )  → ((OpShelfTerm2 n A )  → (OpShelfTerm2 n A ) )) 
  
  simplifyB : (ShelfTerm  → ShelfTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (<|L x1 x2 )  = (<|L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClShelfTerm A ) → (ClShelfTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (<|Cl x1 x2 )  = (<|Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpShelfTerm n ) → (OpShelfTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (<|OL x1 x2 )  = (<|OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpShelfTerm2 n A ) → (OpShelfTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (<|OL2 x1 x2 )  = (<|OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Shelf A ) → (ShelfTerm  → A )))
  evalB Sh (|>L x1 x2 )  = ((|> Sh ) (evalB Sh x1 ) (evalB Sh x2 ) )
  
  evalB Sh (<|L x1 x2 )  = ((<| Sh ) (evalB Sh x1 ) (evalB Sh x2 ) )
  
  evalCl : ({A  : Set }  → ((Shelf A ) → ((ClShelfTerm A ) → A )))
  evalCl Sh (sing x1 )  = x1 
  
  evalCl Sh (|>Cl x1 x2 )  = ((|> Sh ) (evalCl Sh x1 ) (evalCl Sh x2 ) )
  
  evalCl Sh (<|Cl x1 x2 )  = ((<| Sh ) (evalCl Sh x1 ) (evalCl Sh x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Shelf A ) → ((Vec A n ) → ((OpShelfTerm n ) → A ))))
  evalOp n Sh vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Sh vars (|>OL x1 x2 )  = ((|> Sh ) (evalOp n Sh vars x1 ) (evalOp n Sh vars x2 ) )
  
  evalOp n Sh vars (<|OL x1 x2 )  = ((<| Sh ) (evalOp n Sh vars x1 ) (evalOp n Sh vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Shelf A ) → ((Vec A n ) → ((OpShelfTerm2 n A ) → A ))))
  evalOpE n Sh vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Sh vars (sing2 x1 )  = x1 
  
  evalOpE n Sh vars (|>OL2 x1 x2 )  = ((|> Sh ) (evalOpE n Sh vars x1 ) (evalOpE n Sh vars x2 ) )
  
  evalOpE n Sh vars (<|OL2 x1 x2 )  = ((<| Sh ) (evalOpE n Sh vars x1 ) (evalOpE n Sh vars x2 ) )
  
  inductionB : ((P  : (ShelfTerm  → Set ))  → (((x1 x2  : ShelfTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → (((x1 x2  : ShelfTerm  )  → ((P x1 ) → ((P x2 ) → (P (<|L x1 x2 ) )))) → ((x  : ShelfTerm )  → (P x )))))
  inductionB p p|>l p<|l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionB p p|>l p<|l (<|L x1 x2 )  = (p<|l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClShelfTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClShelfTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → (((x1 x2  : (ClShelfTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (<|Cl x1 x2 ) )))) → ((x  : (ClShelfTerm A ))  → (P x ))))))
  inductionCl _ p psing p|>cl p<|cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2 )  = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpShelfTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpShelfTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → (((x1 x2  : (OpShelfTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL x1 x2 ) )))) → ((x  : (OpShelfTerm n ))  → (P x ))))))
  inductionOp _ p pv p|>ol p<|ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol p<|ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOp _ p pv p|>ol p<|ol (<|OL x1 x2 )  = (p<|ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpShelfTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpShelfTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → (((x1 x2  : (OpShelfTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL2 x1 x2 ) )))) → ((x  : (OpShelfTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2 )  = (p<|ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  |>L' : (  (ShelfTerm   → (ShelfTerm   → ShelfTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  <|L' : (  (ShelfTerm   → (ShelfTerm   → ShelfTerm  )))
  <|L' x1 x2  = (<|L x1 x2 )
  
  stageB : (ShelfTerm  → (Staged ShelfTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (<|L x1 x2 )  = (stage2 <|L' (codeLift2 <|L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClShelfTerm A )  → ((ClShelfTerm A )  → (ClShelfTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  <|Cl' : ({A  : Set }  → ((ClShelfTerm A )  → ((ClShelfTerm A )  → (ClShelfTerm A ) )))
  <|Cl' x1 x2  = (<|Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClShelfTerm A ) → (Staged (ClShelfTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (<|Cl x1 x2 )  = (stage2 <|Cl' (codeLift2 <|Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpShelfTerm n )  → ((OpShelfTerm n )  → (OpShelfTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  <|OL' : ({n  : Nat}  → ((OpShelfTerm n )  → ((OpShelfTerm n )  → (OpShelfTerm n ) )))
  <|OL' x1 x2  = (<|OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpShelfTerm n ) → (Staged (OpShelfTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (<|OL x1 x2 )  = (stage2 <|OL' (codeLift2 <|OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpShelfTerm2 n A )  → ((OpShelfTerm2 n A )  → (OpShelfTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  <|OL2' : ({n  : Nat } {A  : Set }  → ((OpShelfTerm2 n A )  → ((OpShelfTerm2 n A )  → (OpShelfTerm2 n A ) )))
  <|OL2' x1 x2  = (<|OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpShelfTerm2 n A ) → (Staged (OpShelfTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (<|OL2 x1 x2 )  = (stage2 <|OL2' (codeLift2 <|OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      <|T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   