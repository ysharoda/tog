
module LeftSpindle   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLeftSpindle  (A : Set) (|> : (A → (A → A))) : Set where 
     field  
      leftDistributive : ( {x y z : A} → (|> x (|> y z)) ≡ (|> (|> x y) (|> x z))) 
      idempotent_|> : ( {x : A} → (|> x x) ≡ x)  
  
  record LeftSpindle  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      isLeftSpindle : (IsLeftSpindle A |>)  
  
  open LeftSpindle
  record Sig  (AS : Set) : Set where 
     field  
      |>S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftDistributiveP : ( {xP yP zP : (Prod A A)} → (|>P xP (|>P yP zP)) ≡ (|>P (|>P xP yP) (|>P xP zP))) 
      idempotent_|>P : ( {xP : (Prod A A)} → (|>P xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Le1 : (LeftSpindle A1)) (Le2 : (LeftSpindle A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Le1) x1 x2)) ≡ ((|> Le2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Le1 : (LeftSpindle A1)) (Le2 : (LeftSpindle A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Le1) x1 x2) ((|> Le2) y1 y2)))))  
  
  data LeftSpindleTerm   : Set where 
      |>L : (LeftSpindleTerm → (LeftSpindleTerm → LeftSpindleTerm))  
      
  data ClLeftSpindleTerm  (A : Set) : Set where 
      sing : (A → (ClLeftSpindleTerm A)) 
      |>Cl : ((ClLeftSpindleTerm A) → ((ClLeftSpindleTerm A) → (ClLeftSpindleTerm A)))  
      
  data OpLeftSpindleTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLeftSpindleTerm n)) 
      |>OL : ((OpLeftSpindleTerm n) → ((OpLeftSpindleTerm n) → (OpLeftSpindleTerm n)))  
      
  data OpLeftSpindleTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLeftSpindleTerm2 n A)) 
      sing2 : (A → (OpLeftSpindleTerm2 n A)) 
      |>OL2 : ((OpLeftSpindleTerm2 n A) → ((OpLeftSpindleTerm2 n A) → (OpLeftSpindleTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClLeftSpindleTerm A) → (ClLeftSpindleTerm A)) 
  simplifyCl _ (|>Cl x1 x2) = (|>Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpLeftSpindleTerm n) → (OpLeftSpindleTerm n)) 
  simplifyOpB _ (|>OL x1 x2) = (|>OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpLeftSpindleTerm2 n A) → (OpLeftSpindleTerm2 n A)) 
  simplifyOp _ _ (|>OL2 x1 x2) = (|>OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((LeftSpindle A) → (LeftSpindleTerm → A)) 
  evalB Le (|>L x1 x2) = ((|> Le) (evalB Le x1) (evalB Le x2))  
  evalCl :  {A : Set} →  ((LeftSpindle A) → ((ClLeftSpindleTerm A) → A)) 
  evalCl Le (sing x1) = x1  
  evalCl Le (|>Cl x1 x2) = ((|> Le) (evalCl Le x1) (evalCl Le x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((LeftSpindle A) → ((Vec A n) → ((OpLeftSpindleTerm n) → A))) 
  evalOpB n Le vars (v x1) = (lookup vars x1)  
  evalOpB n Le vars (|>OL x1 x2) = ((|> Le) (evalOpB n Le vars x1) (evalOpB n Le vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((LeftSpindle A) → ((Vec A n) → ((OpLeftSpindleTerm2 n A) → A))) 
  evalOp n Le vars (v2 x1) = (lookup vars x1)  
  evalOp n Le vars (sing2 x1) = x1  
  evalOp n Le vars (|>OL2 x1 x2) = ((|> Le) (evalOp n Le vars x1) (evalOp n Le vars x2))  
  inductionB :  (P : (LeftSpindleTerm → Set)) →  (( (x1 x2 : LeftSpindleTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → ( (x : LeftSpindleTerm) → (P x))) 
  inductionB p p|>l (|>L x1 x2) = (p|>l _ _ (inductionB p p|>l x1) (inductionB p p|>l x2))  
  inductionCl :  (A : Set) (P : ((ClLeftSpindleTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLeftSpindleTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → ( (x : (ClLeftSpindleTerm A)) → (P x)))) 
  inductionCl _ p psing p|>cl (sing x1) = (psing x1)  
  inductionCl _ p psing p|>cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl _ p psing p|>cl x1) (inductionCl _ p psing p|>cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpLeftSpindleTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLeftSpindleTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → ( (x : (OpLeftSpindleTerm n)) → (P x)))) 
  inductionOpB _ p pv p|>ol (v x1) = (pv x1)  
  inductionOpB _ p pv p|>ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB _ p pv p|>ol x1) (inductionOpB _ p pv p|>ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpLeftSpindleTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLeftSpindleTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → ( (x : (OpLeftSpindleTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 p|>ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p|>ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p|>ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp _ _ p pv2 psing2 p|>ol2 x1) (inductionOp _ _ p pv2 psing2 p|>ol2 x2))  
  stageB :  (LeftSpindleTerm → (Staged LeftSpindleTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClLeftSpindleTerm A) → (Staged (ClLeftSpindleTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpLeftSpindleTerm n) → (Staged (OpLeftSpindleTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpLeftSpindleTerm2 n A) → (Staged (OpLeftSpindleTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 