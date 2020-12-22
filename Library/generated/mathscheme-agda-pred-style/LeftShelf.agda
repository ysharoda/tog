
module LeftShelf   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftShelf  (A : Set) (|> : (A → (A → A))) : Set where 
     field  
      leftDistributive : ( {x y z : A} → (|> x (|> y z)) ≡ (|> (|> x y) (|> x z)))  
  
  record LeftShelf  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      isLeftShelf : (IsLeftShelf A |>)  
  
  open LeftShelf
  record Sig  (AS : Set) : Set where 
     field  
      |>S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftDistributiveP : ( {xP yP zP : (Prod A A)} → (|>P xP (|>P yP zP)) ≡ (|>P (|>P xP yP) (|>P xP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftShelf A1)) (Le2 : (LeftShelf A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Le1) x1 x2)) ≡ ((|> Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftShelf A1)) (Le2 : (LeftShelf A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Le1) x1 x2) ((|> Le2) y1 y2)))))  
  
  data LeftShelfTerm   : Set where 
      |>L : (LeftShelfTerm → (LeftShelfTerm → LeftShelfTerm))  
      
  data ClLeftShelfTerm  (A : Set) : Set where 
      sing : (A → (ClLeftShelfTerm A)) 
      |>Cl : ((ClLeftShelfTerm A) → ((ClLeftShelfTerm A) → (ClLeftShelfTerm A)))  
      
  data OpLeftShelfTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftShelfTerm n)) 
      |>OL : ((OpLeftShelfTerm n) → ((OpLeftShelfTerm n) → (OpLeftShelfTerm n)))  
      
  data OpLeftShelfTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftShelfTerm2 n A)) 
      sing2 : (A → (OpLeftShelfTerm2 n A)) 
      |>OL2 : ((OpLeftShelfTerm2 n A) → ((OpLeftShelfTerm2 n A) → (OpLeftShelfTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClLeftShelfTerm A) → (ClLeftShelfTerm A)) 
  simplifyCl _ (|>Cl x1 x2) = (|>Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpLeftShelfTerm n) → (OpLeftShelfTerm n)) 
  simplifyOpB _ (|>OL x1 x2) = (|>OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpLeftShelfTerm2 n A) → (OpLeftShelfTerm2 n A)) 
  simplifyOp _ _ (|>OL2 x1 x2) = (|>OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftShelf A) → (LeftShelfTerm → A)) 
  evalB Le (|>L x1 x2) = ((|> Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftShelf A) → ((ClLeftShelfTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (|>Cl x1 x2) = ((|> Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((LeftShelf A) → ((Vec A n) → ((OpLeftShelfTerm n) → A))) 
  evalOpB n Le vars (v x1) = (lookup vars x1)  
  evalOpB n Le vars (|>OL x1 x2) = ((|> Le) (evalOpB n Le vars x1) (evalOpB n Le vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((LeftShelf A) → ((Vec A n) → ((OpLeftShelfTerm2 n A) → A))) 
  evalOp n Le vars (v2 x1) = (lookup vars x1)  
  evalOp n Le vars (sing2 x1) = x1  
  evalOp n Le vars (|>OL2 x1 x2) = ((|> Le) (evalOp n Le vars x1) (evalOp n Le vars x2))  
  inductionB :  (P : (LeftShelfTerm → Set)) →  (( (x1 x2 : LeftShelfTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → ( (x : LeftShelfTerm) → (P x))) 
  inductionB p p|>l (|>L x1 x2) = (p|>l _ _ (inductionB p p|>l x1) (inductionB p p|>l x2))  
  inductionCl :  (A : Set) (P : ((ClLeftShelfTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftShelfTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → ( (x : (ClLeftShelfTerm A)) → (P x)))) 
  inductionCl _ p psing p|>cl (sing x1) = (psing x1)  
  inductionCl _ p psing p|>cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl _ p psing p|>cl x1) (inductionCl _ p psing p|>cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpLeftShelfTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftShelfTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → ( (x : (OpLeftShelfTerm n)) → (P x)))) 
  inductionOpB _ p pv p|>ol (v x1) = (pv x1)  
  inductionOpB _ p pv p|>ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB _ p pv p|>ol x1) (inductionOpB _ p pv p|>ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpLeftShelfTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftShelfTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → ( (x : (OpLeftShelfTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 p|>ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p|>ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p|>ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp _ _ p pv2 psing2 p|>ol2 x1) (inductionOp _ _ p pv2 psing2 p|>ol2 x2))  
  stageB :  (LeftShelfTerm → (Staged LeftShelfTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClLeftShelfTerm A) → (Staged (ClLeftShelfTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpLeftShelfTerm n) → (Staged (OpLeftShelfTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpLeftShelfTerm2 n A) → (Staged (OpLeftShelfTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 