
 module LeftSpindle_Shelf  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftSpindle_Shelf (A  : Set ) (|>  : (A  → (A  → A ))) (<|  : (A  → (A  → A )))  : Set where
    constructor IsLeftSpindle_ShelfC
    field
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) ))
      idempotent_|> : ({x  : A }  → (|> x x ) ≡ x )
      rightDistributive : ({x y z  : A }  → (<| (<| y z ) x ) ≡ (<| (<| y x ) (<| z x ) )) 
  
  record LeftSpindle_Shelf (A  : Set )  : Set where
    constructor LeftSpindle_ShelfC
    field
      |> : (A  → (A  → A ))
      <| : (A  → (A  → A ))
      isLeftSpindle_Shelf : (IsLeftSpindle_Shelf A |> <| ) 
  
  open LeftSpindle_Shelf
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
      idempotent_|>P : ({xP  : (Prod AP AP )}  → (|>P xP xP ) ≡ xP )
      rightDistributiveP : ({xP yP zP  : (Prod AP AP )}  → (<|P (<|P yP zP ) xP ) ≡ (<|P (<|P yP xP ) (<|P zP xP ) )) 
  
  record Hom (A1 A2  : Set ) (Le1  : (LeftSpindle_Shelf A1 )) (Le2  : (LeftSpindle_Shelf A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Le1 ) x1 x2 ) ) ≡ ((|> Le2 ) (hom x1 ) (hom x2 ) ))
      pres-<| : ({x1  : A1} {x2  : A1}  → (hom ((<| Le1 ) x1 x2 ) ) ≡ ((<| Le2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftSpindle_Shelf A1 )) (Le2  : (LeftSpindle_Shelf A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Le1 ) x1 x2 ) ((|> Le2 ) y1 y2 ) ))))
      interp-<| : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((<| Le1 ) x1 x2 ) ((<| Le2 ) y1 y2 ) )))) 
  
  data LeftSpindle_ShelfTerm  : Set where
    |>L : (LeftSpindle_ShelfTerm   → (LeftSpindle_ShelfTerm   → LeftSpindle_ShelfTerm  ))
    <|L : (LeftSpindle_ShelfTerm   → (LeftSpindle_ShelfTerm   → LeftSpindle_ShelfTerm  )) 
  
  data ClLeftSpindle_ShelfTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftSpindle_ShelfTerm A ) )
    |>Cl : ((ClLeftSpindle_ShelfTerm A )  → ((ClLeftSpindle_ShelfTerm A )  → (ClLeftSpindle_ShelfTerm A ) ))
    <|Cl : ((ClLeftSpindle_ShelfTerm A )  → ((ClLeftSpindle_ShelfTerm A )  → (ClLeftSpindle_ShelfTerm A ) )) 
  
  data OpLeftSpindle_ShelfTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftSpindle_ShelfTerm n ) )
    |>OL : ((OpLeftSpindle_ShelfTerm n )  → ((OpLeftSpindle_ShelfTerm n )  → (OpLeftSpindle_ShelfTerm n ) ))
    <|OL : ((OpLeftSpindle_ShelfTerm n )  → ((OpLeftSpindle_ShelfTerm n )  → (OpLeftSpindle_ShelfTerm n ) )) 
  
  data OpLeftSpindle_ShelfTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftSpindle_ShelfTerm2 n A ) )
    sing2 : (A  → (OpLeftSpindle_ShelfTerm2 n A ) )
    |>OL2 : ((OpLeftSpindle_ShelfTerm2 n A )  → ((OpLeftSpindle_ShelfTerm2 n A )  → (OpLeftSpindle_ShelfTerm2 n A ) ))
    <|OL2 : ((OpLeftSpindle_ShelfTerm2 n A )  → ((OpLeftSpindle_ShelfTerm2 n A )  → (OpLeftSpindle_ShelfTerm2 n A ) )) 
  
  simplifyB : (LeftSpindle_ShelfTerm  → LeftSpindle_ShelfTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (<|L x1 x2 )  = (<|L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClLeftSpindle_ShelfTerm A ) → (ClLeftSpindle_ShelfTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (<|Cl x1 x2 )  = (<|Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpLeftSpindle_ShelfTerm n ) → (OpLeftSpindle_ShelfTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (<|OL x1 x2 )  = (<|OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftSpindle_ShelfTerm2 n A ) → (OpLeftSpindle_ShelfTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (<|OL2 x1 x2 )  = (<|OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((LeftSpindle_Shelf A ) → (LeftSpindle_ShelfTerm  → A )))
  evalB Le (|>L x1 x2 )  = ((|> Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalB Le (<|L x1 x2 )  = ((<| Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftSpindle_Shelf A ) → ((ClLeftSpindle_ShelfTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (|>Cl x1 x2 )  = ((|> Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalCl Le (<|Cl x1 x2 )  = ((<| Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftSpindle_Shelf A ) → ((Vec A n ) → ((OpLeftSpindle_ShelfTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (|>OL x1 x2 )  = ((|> Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOp n Le vars (<|OL x1 x2 )  = ((<| Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftSpindle_Shelf A ) → ((Vec A n ) → ((OpLeftSpindle_ShelfTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (|>OL2 x1 x2 )  = ((|> Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  evalOpE n Le vars (<|OL2 x1 x2 )  = ((<| Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftSpindle_ShelfTerm  → Set ))  → (((x1 x2  : LeftSpindle_ShelfTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → (((x1 x2  : LeftSpindle_ShelfTerm  )  → ((P x1 ) → ((P x2 ) → (P (<|L x1 x2 ) )))) → ((x  : LeftSpindle_ShelfTerm )  → (P x )))))
  inductionB p p|>l p<|l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionB p p|>l p<|l (<|L x1 x2 )  = (p<|l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftSpindle_ShelfTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftSpindle_ShelfTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → (((x1 x2  : (ClLeftSpindle_ShelfTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (<|Cl x1 x2 ) )))) → ((x  : (ClLeftSpindle_ShelfTerm A ))  → (P x ))))))
  inductionCl _ p psing p|>cl p<|cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2 )  = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftSpindle_ShelfTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftSpindle_ShelfTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → (((x1 x2  : (OpLeftSpindle_ShelfTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL x1 x2 ) )))) → ((x  : (OpLeftSpindle_ShelfTerm n ))  → (P x ))))))
  inductionOp _ p pv p|>ol p<|ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol p<|ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOp _ p pv p|>ol p<|ol (<|OL x1 x2 )  = (p<|ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftSpindle_ShelfTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftSpindle_ShelfTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → (((x1 x2  : (OpLeftSpindle_ShelfTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL2 x1 x2 ) )))) → ((x  : (OpLeftSpindle_ShelfTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2 )  = (p<|ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  |>L' : (  (LeftSpindle_ShelfTerm   → (LeftSpindle_ShelfTerm   → LeftSpindle_ShelfTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  <|L' : (  (LeftSpindle_ShelfTerm   → (LeftSpindle_ShelfTerm   → LeftSpindle_ShelfTerm  )))
  <|L' x1 x2  = (<|L x1 x2 )
  
  stageB : (LeftSpindle_ShelfTerm  → (Staged LeftSpindle_ShelfTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (<|L x1 x2 )  = (stage2 <|L' (codeLift2 <|L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClLeftSpindle_ShelfTerm A )  → ((ClLeftSpindle_ShelfTerm A )  → (ClLeftSpindle_ShelfTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  <|Cl' : ({A  : Set }  → ((ClLeftSpindle_ShelfTerm A )  → ((ClLeftSpindle_ShelfTerm A )  → (ClLeftSpindle_ShelfTerm A ) )))
  <|Cl' x1 x2  = (<|Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftSpindle_ShelfTerm A ) → (Staged (ClLeftSpindle_ShelfTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (<|Cl x1 x2 )  = (stage2 <|Cl' (codeLift2 <|Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpLeftSpindle_ShelfTerm n )  → ((OpLeftSpindle_ShelfTerm n )  → (OpLeftSpindle_ShelfTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  <|OL' : ({n  : Nat}  → ((OpLeftSpindle_ShelfTerm n )  → ((OpLeftSpindle_ShelfTerm n )  → (OpLeftSpindle_ShelfTerm n ) )))
  <|OL' x1 x2  = (<|OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftSpindle_ShelfTerm n ) → (Staged (OpLeftSpindle_ShelfTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (<|OL x1 x2 )  = (stage2 <|OL' (codeLift2 <|OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpLeftSpindle_ShelfTerm2 n A )  → ((OpLeftSpindle_ShelfTerm2 n A )  → (OpLeftSpindle_ShelfTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  <|OL2' : ({n  : Nat } {A  : Set }  → ((OpLeftSpindle_ShelfTerm2 n A )  → ((OpLeftSpindle_ShelfTerm2 n A )  → (OpLeftSpindle_ShelfTerm2 n A ) )))
  <|OL2' x1 x2  = (<|OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftSpindle_ShelfTerm2 n A ) → (Staged (OpLeftSpindle_ShelfTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (<|OL2 x1 x2 )  = (stage2 <|OL2' (codeLift2 <|OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      <|T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
