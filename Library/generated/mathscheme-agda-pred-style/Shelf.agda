
module Shelf   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsShelf  (A : Set) (|> : (A → (A → A))) (<| : (A → (A → A))) : Set where 
     field  
      leftDistributive : ( {x y z : A} → (|> x (|> y z)) ≡ (|> (|> x y) (|> x z))) 
      rightDistributive : ( {x y z : A} → (<| (<| y z) x) ≡ (<| (<| y x) (<| z x)))  
  
  record Shelf  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      <| : (A → (A → A)) 
      isShelf : (IsShelf A |> <|)  
  
  open Shelf
  record Sig  (AS : Set) : Set where 
     field  
      |>S : (AS → (AS → AS)) 
      <|S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      <|P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftDistributiveP : ( {xP yP zP : (Prod A A)} → (|>P xP (|>P yP zP)) ≡ (|>P (|>P xP yP) (|>P xP zP))) 
      rightDistributiveP : ( {xP yP zP : (Prod A A)} → (<|P (<|P yP zP) xP) ≡ (<|P (<|P yP xP) (<|P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Sh1 : (Shelf A1)) (Sh2 : (Shelf A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Sh1) x1 x2)) ≡ ((|> Sh2) (hom x1) (hom x2))) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Sh1) x1 x2)) ≡ ((<| Sh2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Sh1 : (Shelf A1)) (Sh2 : (Shelf A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Sh1) x1 x2) ((|> Sh2) y1 y2))))) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Sh1) x1 x2) ((<| Sh2) y1 y2)))))  
  
  data ShelfTerm   : Set where 
      |>L : (ShelfTerm → (ShelfTerm → ShelfTerm)) 
      <|L : (ShelfTerm → (ShelfTerm → ShelfTerm))  
      
  data ClShelfTerm  (A : Set) : Set where 
      sing : (A → (ClShelfTerm A)) 
      |>Cl : ((ClShelfTerm A) → ((ClShelfTerm A) → (ClShelfTerm A))) 
      <|Cl : ((ClShelfTerm A) → ((ClShelfTerm A) → (ClShelfTerm A)))  
      
  data OpShelfTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpShelfTerm n)) 
      |>OL : ((OpShelfTerm n) → ((OpShelfTerm n) → (OpShelfTerm n))) 
      <|OL : ((OpShelfTerm n) → ((OpShelfTerm n) → (OpShelfTerm n)))  
      
  data OpShelfTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpShelfTerm2 n A)) 
      sing2 : (A → (OpShelfTerm2 n A)) 
      |>OL2 : ((OpShelfTerm2 n A) → ((OpShelfTerm2 n A) → (OpShelfTerm2 n A))) 
      <|OL2 : ((OpShelfTerm2 n A) → ((OpShelfTerm2 n A) → (OpShelfTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClShelfTerm A) → (ClShelfTerm A)) 
  simplifyCl _ (|>Cl x1 x2) = (|>Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (<|Cl x1 x2) = (<|Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpShelfTerm n) → (OpShelfTerm n)) 
  simplifyOpB _ (|>OL x1 x2) = (|>OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (<|OL x1 x2) = (<|OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpShelfTerm2 n A) → (OpShelfTerm2 n A)) 
  simplifyOp _ _ (|>OL2 x1 x2) = (|>OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (<|OL2 x1 x2) = (<|OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Shelf A) → (ShelfTerm → A)) 
  evalB Sh (|>L x1 x2) = ((|> Sh) (evalB Sh x1) (evalB Sh x2))  
  evalB Sh (<|L x1 x2) = ((<| Sh) (evalB Sh x1) (evalB Sh x2))  
  evalCl :  {A : Set} →  ((Shelf A) → ((ClShelfTerm A) → A)) 
  evalCl Sh (sing x1) = x1  
  evalCl Sh (|>Cl x1 x2) = ((|> Sh) (evalCl Sh x1) (evalCl Sh x2))  
  evalCl Sh (<|Cl x1 x2) = ((<| Sh) (evalCl Sh x1) (evalCl Sh x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Shelf A) → ((Vec A n) → ((OpShelfTerm n) → A))) 
  evalOpB n Sh vars (v x1) = (lookup vars x1)  
  evalOpB n Sh vars (|>OL x1 x2) = ((|> Sh) (evalOpB n Sh vars x1) (evalOpB n Sh vars x2))  
  evalOpB n Sh vars (<|OL x1 x2) = ((<| Sh) (evalOpB n Sh vars x1) (evalOpB n Sh vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Shelf A) → ((Vec A n) → ((OpShelfTerm2 n A) → A))) 
  evalOp n Sh vars (v2 x1) = (lookup vars x1)  
  evalOp n Sh vars (sing2 x1) = x1  
  evalOp n Sh vars (|>OL2 x1 x2) = ((|> Sh) (evalOp n Sh vars x1) (evalOp n Sh vars x2))  
  evalOp n Sh vars (<|OL2 x1 x2) = ((<| Sh) (evalOp n Sh vars x1) (evalOp n Sh vars x2))  
  inductionB :  (P : (ShelfTerm → Set)) →  (( (x1 x2 : ShelfTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → (( (x1 x2 : ShelfTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → ( (x : ShelfTerm) → (P x)))) 
  inductionB p p|>l p<|l (|>L x1 x2) = (p|>l _ _ (inductionB p p|>l p<|l x1) (inductionB p p|>l p<|l x2))  
  inductionB p p|>l p<|l (<|L x1 x2) = (p<|l _ _ (inductionB p p|>l p<|l x1) (inductionB p p|>l p<|l x2))  
  inductionCl :  (A : Set) (P : ((ClShelfTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClShelfTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → (( (x1 x2 : (ClShelfTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → ( (x : (ClShelfTerm A)) → (P x))))) 
  inductionCl _ p psing p|>cl p<|cl (sing x1) = (psing x1)  
  inductionCl _ p psing p|>cl p<|cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl _ p psing p|>cl p<|cl x1) (inductionCl _ p psing p|>cl p<|cl x2))  
  inductionCl _ p psing p|>cl p<|cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl _ p psing p|>cl p<|cl x1) (inductionCl _ p psing p|>cl p<|cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpShelfTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpShelfTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → (( (x1 x2 : (OpShelfTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → ( (x : (OpShelfTerm n)) → (P x))))) 
  inductionOpB _ p pv p|>ol p<|ol (v x1) = (pv x1)  
  inductionOpB _ p pv p|>ol p<|ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB _ p pv p|>ol p<|ol x1) (inductionOpB _ p pv p|>ol p<|ol x2))  
  inductionOpB _ p pv p|>ol p<|ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB _ p pv p|>ol p<|ol x1) (inductionOpB _ p pv p|>ol p<|ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpShelfTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpShelfTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → (( (x1 x2 : (OpShelfTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → ( (x : (OpShelfTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 x2))  
  inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp _ _ p pv2 psing2 p|>ol2 p<|ol2 x2))  
  stageB :  (ShelfTerm → (Staged ShelfTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClShelfTerm A) → (Staged (ClShelfTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpShelfTerm n) → (Staged (OpShelfTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpShelfTerm2 n A) → (Staged (OpShelfTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A))) 
      <|T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 