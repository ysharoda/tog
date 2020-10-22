
 module Spindle  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsSpindle (A  : Set ) (|>  : (A  → (A  → A ))) (<|  : (A  → (A  → A )))  : Set where
    constructor IsSpindleC
    field
      leftDistributive : ({x y z  : A }  → (|> x (|> y z ) ) ≡ (|> (|> x y ) (|> x z ) ))
      rightDistributive : ({x y z  : A }  → (<| (<| y z ) x ) ≡ (<| (<| y x ) (<| z x ) ))
      idempotent_|> : ({x  : A }  → (|> x x ) ≡ x )
      idempotent_<| : ({x  : A }  → (<| x x ) ≡ x ) 
  
  record Spindle (A  : Set )  : Set where
    constructor SpindleC
    field
      |> : (A  → (A  → A ))
      <| : (A  → (A  → A ))
      isSpindle : (IsSpindle A |> <| ) 
  
  open Spindle
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
      idempotent_|>P : ({xP  : (Prod AP AP )}  → (|>P xP xP ) ≡ xP )
      idempotent_<|P : ({xP  : (Prod AP AP )}  → (<|P xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Sp1  : (Spindle A1 )) (Sp2  : (Spindle A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Sp1 ) x1 x2 ) ) ≡ ((|> Sp2 ) (hom x1 ) (hom x2 ) ))
      pres-<| : ({x1  : A1} {x2  : A1}  → (hom ((<| Sp1 ) x1 x2 ) ) ≡ ((<| Sp2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Sp1  : (Spindle A1 )) (Sp2  : (Spindle A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Sp1 ) x1 x2 ) ((|> Sp2 ) y1 y2 ) ))))
      interp-<| : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((<| Sp1 ) x1 x2 ) ((<| Sp2 ) y1 y2 ) )))) 
  
  data SpindleTerm  : Set where
    |>L : (SpindleTerm   → (SpindleTerm   → SpindleTerm  ))
    <|L : (SpindleTerm   → (SpindleTerm   → SpindleTerm  )) 
  
  data ClSpindleTerm (A  : Set )  : Set where
    sing : (A  → (ClSpindleTerm A ) )
    |>Cl : ((ClSpindleTerm A )  → ((ClSpindleTerm A )  → (ClSpindleTerm A ) ))
    <|Cl : ((ClSpindleTerm A )  → ((ClSpindleTerm A )  → (ClSpindleTerm A ) )) 
  
  data OpSpindleTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpSpindleTerm n ) )
    |>OL : ((OpSpindleTerm n )  → ((OpSpindleTerm n )  → (OpSpindleTerm n ) ))
    <|OL : ((OpSpindleTerm n )  → ((OpSpindleTerm n )  → (OpSpindleTerm n ) )) 
  
  data OpSpindleTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpSpindleTerm2 n A ) )
    sing2 : (A  → (OpSpindleTerm2 n A ) )
    |>OL2 : ((OpSpindleTerm2 n A )  → ((OpSpindleTerm2 n A )  → (OpSpindleTerm2 n A ) ))
    <|OL2 : ((OpSpindleTerm2 n A )  → ((OpSpindleTerm2 n A )  → (OpSpindleTerm2 n A ) )) 
  
  simplifyB : (SpindleTerm  → SpindleTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (<|L x1 x2 )  = (<|L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClSpindleTerm A ) → (ClSpindleTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (<|Cl x1 x2 )  = (<|Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpSpindleTerm n ) → (OpSpindleTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (<|OL x1 x2 )  = (<|OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpSpindleTerm2 n A ) → (OpSpindleTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (<|OL2 x1 x2 )  = (<|OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Spindle A ) → (SpindleTerm  → A )))
  evalB Sp (|>L x1 x2 )  = ((|> Sp ) (evalB Sp x1 ) (evalB Sp x2 ) )
  
  evalB Sp (<|L x1 x2 )  = ((<| Sp ) (evalB Sp x1 ) (evalB Sp x2 ) )
  
  evalCl : ({A  : Set }  → ((Spindle A ) → ((ClSpindleTerm A ) → A )))
  evalCl Sp (sing x1 )  = x1 
  
  evalCl Sp (|>Cl x1 x2 )  = ((|> Sp ) (evalCl Sp x1 ) (evalCl Sp x2 ) )
  
  evalCl Sp (<|Cl x1 x2 )  = ((<| Sp ) (evalCl Sp x1 ) (evalCl Sp x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Spindle A ) → ((Vec A n ) → ((OpSpindleTerm n ) → A ))))
  evalOp n Sp vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Sp vars (|>OL x1 x2 )  = ((|> Sp ) (evalOp n Sp vars x1 ) (evalOp n Sp vars x2 ) )
  
  evalOp n Sp vars (<|OL x1 x2 )  = ((<| Sp ) (evalOp n Sp vars x1 ) (evalOp n Sp vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Spindle A ) → ((Vec A n ) → ((OpSpindleTerm2 n A ) → A ))))
  evalOpE n Sp vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Sp vars (sing2 x1 )  = x1 
  
  evalOpE n Sp vars (|>OL2 x1 x2 )  = ((|> Sp ) (evalOpE n Sp vars x1 ) (evalOpE n Sp vars x2 ) )
  
  evalOpE n Sp vars (<|OL2 x1 x2 )  = ((<| Sp ) (evalOpE n Sp vars x1 ) (evalOpE n Sp vars x2 ) )
  
  inductionB : ((P  : (SpindleTerm  → Set ))  → (((x1 x2  : SpindleTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → (((x1 x2  : SpindleTerm  )  → ((P x1 ) → ((P x2 ) → (P (<|L x1 x2 ) )))) → ((x  : SpindleTerm )  → (P x )))))
  inductionB p p|>l p<|l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionB p p|>l p<|l (<|L x1 x2 )  = (p<|l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClSpindleTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClSpindleTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → (((x1 x2  : (ClSpindleTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (<|Cl x1 x2 ) )))) → ((x  : (ClSpindleTerm A ))  → (P x ))))))
  inductionCl _ p psing p|>cl p<|cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2 )  = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpSpindleTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpSpindleTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → (((x1 x2  : (OpSpindleTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL x1 x2 ) )))) → ((x  : (OpSpindleTerm n ))  → (P x ))))))
  inductionOp _ p pv p|>ol p<|ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol p<|ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOp _ p pv p|>ol p<|ol (<|OL x1 x2 )  = (p<|ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpSpindleTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpSpindleTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → (((x1 x2  : (OpSpindleTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL2 x1 x2 ) )))) → ((x  : (OpSpindleTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2 )  = (p<|ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  |>L' : (  (SpindleTerm   → (SpindleTerm   → SpindleTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  <|L' : (  (SpindleTerm   → (SpindleTerm   → SpindleTerm  )))
  <|L' x1 x2  = (<|L x1 x2 )
  
  stageB : (SpindleTerm  → (Staged SpindleTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (<|L x1 x2 )  = (stage2 <|L' (codeLift2 <|L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClSpindleTerm A )  → ((ClSpindleTerm A )  → (ClSpindleTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  <|Cl' : ({A  : Set }  → ((ClSpindleTerm A )  → ((ClSpindleTerm A )  → (ClSpindleTerm A ) )))
  <|Cl' x1 x2  = (<|Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClSpindleTerm A ) → (Staged (ClSpindleTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (<|Cl x1 x2 )  = (stage2 <|Cl' (codeLift2 <|Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpSpindleTerm n )  → ((OpSpindleTerm n )  → (OpSpindleTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  <|OL' : ({n  : Nat}  → ((OpSpindleTerm n )  → ((OpSpindleTerm n )  → (OpSpindleTerm n ) )))
  <|OL' x1 x2  = (<|OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpSpindleTerm n ) → (Staged (OpSpindleTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (<|OL x1 x2 )  = (stage2 <|OL' (codeLift2 <|OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpSpindleTerm2 n A )  → ((OpSpindleTerm2 n A )  → (OpSpindleTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  <|OL2' : ({n  : Nat } {A  : Set }  → ((OpSpindleTerm2 n A )  → ((OpSpindleTerm2 n A )  → (OpSpindleTerm2 n A ) )))
  <|OL2' x1 x2  = (<|OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpSpindleTerm2 n A ) → (Staged (OpSpindleTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (<|OL2 x1 x2 )  = (stage2 <|OL2' (codeLift2 <|OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      <|T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
