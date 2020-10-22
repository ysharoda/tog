
 module LeftShelfSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftShelfSig (A  : Set ) (|>  : (A  → (A  → A )))  : Set where
    constructor IsLeftShelfSigC
   
  
  record LeftShelfSig (A  : Set )  : Set where
    constructor LeftShelfSigC
    field
      |> : (A  → (A  → A ))
      isLeftShelfSig : (IsLeftShelfSig A |> ) 
  
  open LeftShelfSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      |>S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      |>P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (Le1  : (LeftShelfSig A1 )) (Le2  : (LeftShelfSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-|> : ({x1  : A1} {x2  : A1}  → (hom ((|> Le1 ) x1 x2 ) ) ≡ ((|> Le2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftShelfSig A1 )) (Le2  : (LeftShelfSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-|> : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((|> Le1 ) x1 x2 ) ((|> Le2 ) y1 y2 ) )))) 
  
  data LeftShelfSigTerm  : Set where
    |>L : (LeftShelfSigTerm   → (LeftShelfSigTerm   → LeftShelfSigTerm  )) 
  
  data ClLeftShelfSigTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftShelfSigTerm A ) )
    |>Cl : ((ClLeftShelfSigTerm A )  → ((ClLeftShelfSigTerm A )  → (ClLeftShelfSigTerm A ) )) 
  
  data OpLeftShelfSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftShelfSigTerm n ) )
    |>OL : ((OpLeftShelfSigTerm n )  → ((OpLeftShelfSigTerm n )  → (OpLeftShelfSigTerm n ) )) 
  
  data OpLeftShelfSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftShelfSigTerm2 n A ) )
    sing2 : (A  → (OpLeftShelfSigTerm2 n A ) )
    |>OL2 : ((OpLeftShelfSigTerm2 n A )  → ((OpLeftShelfSigTerm2 n A )  → (OpLeftShelfSigTerm2 n A ) )) 
  
  simplifyB : (LeftShelfSigTerm  → LeftShelfSigTerm )
  simplifyB (|>L x1 x2 )  = (|>L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClLeftShelfSigTerm A ) → (ClLeftShelfSigTerm A )))
  simplifyCl _ (|>Cl x1 x2 )  = (|>Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpLeftShelfSigTerm n ) → (OpLeftShelfSigTerm n )))
  simplifyOp _ (|>OL x1 x2 )  = (|>OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftShelfSigTerm2 n A ) → (OpLeftShelfSigTerm2 n A )))
  simplifyOpE _ _ (|>OL2 x1 x2 )  = (|>OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((LeftShelfSig A ) → (LeftShelfSigTerm  → A )))
  evalB Le (|>L x1 x2 )  = ((|> Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftShelfSig A ) → ((ClLeftShelfSigTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (|>Cl x1 x2 )  = ((|> Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftShelfSig A ) → ((Vec A n ) → ((OpLeftShelfSigTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (|>OL x1 x2 )  = ((|> Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftShelfSig A ) → ((Vec A n ) → ((OpLeftShelfSigTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (|>OL2 x1 x2 )  = ((|> Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftShelfSigTerm  → Set ))  → (((x1 x2  : LeftShelfSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (|>L x1 x2 ) )))) → ((x  : LeftShelfSigTerm )  → (P x ))))
  inductionB p p|>l (|>L x1 x2 )  = (p|>l _ _ (inductionB p p|>l x1 ) (inductionB p p|>l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftShelfSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftShelfSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (|>Cl x1 x2 ) )))) → ((x  : (ClLeftShelfSigTerm A ))  → (P x )))))
  inductionCl _ p psing p|>cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p|>cl (|>Cl x1 x2 )  = (p|>cl _ _ (inductionCl _ p psing p|>cl x1 ) (inductionCl _ p psing p|>cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftShelfSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftShelfSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL x1 x2 ) )))) → ((x  : (OpLeftShelfSigTerm n ))  → (P x )))))
  inductionOp _ p pv p|>ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p|>ol (|>OL x1 x2 )  = (p|>ol _ _ (inductionOp _ p pv p|>ol x1 ) (inductionOp _ p pv p|>ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftShelfSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftShelfSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (|>OL2 x1 x2 ) )))) → ((x  : (OpLeftShelfSigTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p|>ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p|>ol2 (|>OL2 x1 x2 )  = (p|>ol2 _ _ (inductionOpE _ _ p pv2 psing2 p|>ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p|>ol2 x2 ) )
  
  |>L' : (  (LeftShelfSigTerm   → (LeftShelfSigTerm   → LeftShelfSigTerm  )))
  |>L' x1 x2  = (|>L x1 x2 )
  
  stageB : (LeftShelfSigTerm  → (Staged LeftShelfSigTerm  ))
  stageB (|>L x1 x2 )  = (stage2 |>L' (codeLift2 |>L' ) (stageB  x1 ) (stageB  x2 ) )
  
  |>Cl' : ({A  : Set }  → ((ClLeftShelfSigTerm A )  → ((ClLeftShelfSigTerm A )  → (ClLeftShelfSigTerm A ) )))
  |>Cl' x1 x2  = (|>Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftShelfSigTerm A ) → (Staged (ClLeftShelfSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (|>Cl x1 x2 )  = (stage2 |>Cl' (codeLift2 |>Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  |>OL' : ({n  : Nat}  → ((OpLeftShelfSigTerm n )  → ((OpLeftShelfSigTerm n )  → (OpLeftShelfSigTerm n ) )))
  |>OL' x1 x2  = (|>OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftShelfSigTerm n ) → (Staged (OpLeftShelfSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (|>OL x1 x2 )  = (stage2 |>OL' (codeLift2 |>OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  |>OL2' : ({n  : Nat } {A  : Set }  → ((OpLeftShelfSigTerm2 n A )  → ((OpLeftShelfSigTerm2 n A )  → (OpLeftShelfSigTerm2 n A ) )))
  |>OL2' x1 x2  = (|>OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftShelfSigTerm2 n A ) → (Staged (OpLeftShelfSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (|>OL2 x1 x2 )  = (stage2 |>OL2' (codeLift2 |>OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      |>T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
