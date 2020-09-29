
 module BinaryInverse  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BinaryInverse (A  : Set )  : Set where
    constructor BinaryInverseC
    field
      |> : (A  → (A  → A ))
      <| : (A  → (A  → A ))
      leftInverse : ({x y  : A }  → (<| (|> x y ) x ) ≡ y )
      rightInverse : ({x y  : A }  → (|> x (<| y x ) ) ≡ y ) 
  
  open BinaryInverse
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
      leftInverseP : ({xP yP  : (Prod AP AP )}  → (<|P (|>P xP yP ) xP ) ≡ yP )
      rightInverseP : ({xP yP  : (Prod AP AP )}  → (|>P xP (<|P yP xP ) ) ≡ yP ) 
  
  record Hom (A1 A2  : Set ) (Bi1  : (BinaryInverse A1 )) (Bi2  : (BinaryInverse A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Bi1 ) x1 x2 ) ) ≡ ((|> Bi2 ) (hom x1 ) (hom x2 ) ))
      pres-<| : ({x1  : A1} {x2  : A1}  → (hom ((<| Bi1 ) x1 x2 ) ) ≡ ((<| Bi2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Bi1  : (BinaryInverse A1 )) (Bi2  : (BinaryInverse A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Bi1 ) x1 x2 ) ((|> Bi2 ) y1 y2 ) ))))
      interp-<| : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((<| Bi1 ) x1 x2 ) ((<| Bi2 ) y1 y2 ) )))) 
  
  data BinaryInverseTerm  : Set where
    |>L : (BinaryInverseTerm   → (BinaryInverseTerm   → BinaryInverseTerm  ))
    <|L : (BinaryInverseTerm   → (BinaryInverseTerm   → BinaryInverseTerm  )) 
  
  data ClBinaryInverseTerm (A  : Set )  : Set where
    sing : (A  → (ClBinaryInverseTerm A ) )
    |>Cl : ((ClBinaryInverseTerm A )  → ((ClBinaryInverseTerm A )  → (ClBinaryInverseTerm A ) ))
    <|Cl : ((ClBinaryInverseTerm A )  → ((ClBinaryInverseTerm A )  → (ClBinaryInverseTerm A ) )) 
  
  data OpBinaryInverseTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpBinaryInverseTerm n ) )
    |>OL : ((OpBinaryInverseTerm n )  → ((OpBinaryInverseTerm n )  → (OpBinaryInverseTerm n ) ))
    <|OL : ((OpBinaryInverseTerm n )  → ((OpBinaryInverseTerm n )  → (OpBinaryInverseTerm n ) )) 
  
  data OpBinaryInverseTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpBinaryInverseTerm2 n A ) )
    sing2 : (A  → (OpBinaryInverseTerm2 n A ) )
    |>OL2 : ((OpBinaryInverseTerm2 n A )  → ((OpBinaryInverseTerm2 n A )  → (OpBinaryInverseTerm2 n A ) ))
    <|OL2 : ((OpBinaryInverseTerm2 n A )  → ((OpBinaryInverseTerm2 n A )  → (OpBinaryInverseTerm2 n A ) )) 
  
  simplifyB : (BinaryInverseTerm  → BinaryInverseTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (<|L x1 x2 )  = (<|L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClBinaryInverseTerm A ) → (ClBinaryInverseTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (<|Cl x1 x2 )  = (<|Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpBinaryInverseTerm n ) → (OpBinaryInverseTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (<|OL x1 x2 )  = (<|OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpBinaryInverseTerm2 n A ) → (OpBinaryInverseTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (<|OL2 x1 x2 )  = (<|OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((BinaryInverse A ) → (BinaryInverseTerm  → A )))
  evalB Bi (|>L x1 x2 )  = ((|> Bi ) (evalB Bi x1 ) (evalB Bi x2 ) )
  
  evalB Bi (<|L x1 x2 )  = ((<| Bi ) (evalB Bi x1 ) (evalB Bi x2 ) )
  
  evalCl : ({A  : Set }  → ((BinaryInverse A ) → ((ClBinaryInverseTerm A ) → A )))
  evalCl Bi (sing x1 )  = x1 
  
  evalCl Bi (|>Cl x1 x2 )  = ((|> Bi ) (evalCl Bi x1 ) (evalCl Bi x2 ) )
  
  evalCl Bi (<|Cl x1 x2 )  = ((<| Bi ) (evalCl Bi x1 ) (evalCl Bi x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((BinaryInverse A ) → ((Vec A n ) → ((OpBinaryInverseTerm n ) → A ))))
  evalOp n Bi vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Bi vars (|>OL x1 x2 )  = ((|> Bi ) (evalOp n Bi vars x1 ) (evalOp n Bi vars x2 ) )
  
  evalOp n Bi vars (<|OL x1 x2 )  = ((<| Bi ) (evalOp n Bi vars x1 ) (evalOp n Bi vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((BinaryInverse A ) → ((Vec A n ) → ((OpBinaryInverseTerm2 n A ) → A ))))
  evalOpE n Bi vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Bi vars (sing2 x1 )  = x1 
  
  evalOpE n Bi vars (|>OL2 x1 x2 )  = ((|> Bi ) (evalOpE n Bi vars x1 ) (evalOpE n Bi vars x2 ) )
  
  evalOpE n Bi vars (<|OL2 x1 x2 )  = ((<| Bi ) (evalOpE n Bi vars x1 ) (evalOpE n Bi vars x2 ) )
  
  inductionB : ((P  : (BinaryInverseTerm  → Set ))  → (((x1 x2  : BinaryInverseTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → (((x1 x2  : BinaryInverseTerm  )  → ((P x1 ) → ((P x2 ) → (P (<|L x1 x2 ) )))) → ((x  : BinaryInverseTerm )  → (P x )))))
  inductionB p p|>l p<|l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionB p p|>l p<|l (<|L x1 x2 )  = (p<|l _ _ (inductionB p p|>l p<|l x1 ) (inductionB p p|>l p<|l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClBinaryInverseTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClBinaryInverseTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → (((x1 x2  : (ClBinaryInverseTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (<|Cl x1 x2 ) )))) → ((x  : (ClBinaryInverseTerm A ))  → (P x ))))))
  inductionCl _ p psing p|>cl p<|cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2 )  = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1 ) (inductionCl _ p psing p|>cl p<|cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpBinaryInverseTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpBinaryInverseTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → (((x1 x2  : (OpBinaryInverseTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL x1 x2 ) )))) → ((x  : (OpBinaryInverseTerm n ))  → (P x ))))))
  inductionOp _ p pv p|>ol p<|ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol p<|ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOp _ p pv p|>ol p<|ol (<|OL x1 x2 )  = (p<|ol _ _ (inductionOp _ p pv p|>ol p<|ol x1 ) (inductionOp _ p pv p|>ol p<|ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpBinaryInverseTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpBinaryInverseTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → (((x1 x2  : (OpBinaryInverseTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (<|OL2 x1 x2 ) )))) → ((x  : (OpBinaryInverseTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2 )  = (p<|ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 p<|ol2 x2 ) )
  
  |>L' : (  (BinaryInverseTerm   → (BinaryInverseTerm   → BinaryInverseTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  <|L' : (  (BinaryInverseTerm   → (BinaryInverseTerm   → BinaryInverseTerm  )))
  <|L' x1 x2  = (<|L x1 x2 )
  
  stageB : (BinaryInverseTerm  → (Staged BinaryInverseTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (<|L x1 x2 )  = (stage2 <|L' (codeLift2 <|L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClBinaryInverseTerm A )  → ((ClBinaryInverseTerm A )  → (ClBinaryInverseTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  <|Cl' : ({A  : Set }  → ((ClBinaryInverseTerm A )  → ((ClBinaryInverseTerm A )  → (ClBinaryInverseTerm A ) )))
  <|Cl' x1 x2  = (<|Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClBinaryInverseTerm A ) → (Staged (ClBinaryInverseTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (<|Cl x1 x2 )  = (stage2 <|Cl' (codeLift2 <|Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpBinaryInverseTerm n )  → ((OpBinaryInverseTerm n )  → (OpBinaryInverseTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  <|OL' : ({n  : Nat}  → ((OpBinaryInverseTerm n )  → ((OpBinaryInverseTerm n )  → (OpBinaryInverseTerm n ) )))
  <|OL' x1 x2  = (<|OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpBinaryInverseTerm n ) → (Staged (OpBinaryInverseTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (<|OL x1 x2 )  = (stage2 <|OL' (codeLift2 <|OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpBinaryInverseTerm2 n A )  → ((OpBinaryInverseTerm2 n A )  → (OpBinaryInverseTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  <|OL2' : ({n  : Nat } {A  : Set }  → ((OpBinaryInverseTerm2 n A )  → ((OpBinaryInverseTerm2 n A )  → (OpBinaryInverseTerm2 n A ) )))
  <|OL2' x1 x2  = (<|OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpBinaryInverseTerm2 n A ) → (Staged (OpBinaryInverseTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (<|OL2 x1 x2 )  = (stage2 <|OL2' (codeLift2 <|OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      <|T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
