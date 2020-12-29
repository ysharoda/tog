
module RightSpindle_Shelf   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightSpindle_Shelf  (A : Set) : Set where 
     field  
      <| : (A → (A → A)) 
      rightDistributive : ( {x y z : A} → (<| (<| y z) x) ≡ (<| (<| y x) (<| z x))) 
      idempotent_<| : ( {x : A} → (<| x x) ≡ x) 
      |> : (A → (A → A)) 
      leftDistributive : ( {x y z : A} → (|> x (|> y z)) ≡ (|> (|> x y) (|> x z)))  
  
  open RightSpindle_Shelf
  record Sig  (AS : Set) : Set where 
     field  
      <|S : (AS → (AS → AS)) 
      |>S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      <|P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightDistributiveP : ( {xP yP zP : (Prod A A)} → (<|P (<|P yP zP) xP) ≡ (<|P (<|P yP xP) (<|P zP xP))) 
      idempotent_<|P : ( {xP : (Prod A A)} → (<|P xP xP) ≡ xP) 
      leftDistributiveP : ( {xP yP zP : (Prod A A)} → (|>P xP (|>P yP zP)) ≡ (|>P (|>P xP yP) (|>P xP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightSpindle_Shelf A1)) (Ri2 : (RightSpindle_Shelf A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Ri1) x1 x2)) ≡ ((<| Ri2) (hom x1) (hom x2))) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Ri1) x1 x2)) ≡ ((|> Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightSpindle_Shelf A1)) (Ri2 : (RightSpindle_Shelf A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Ri1) x1 x2) ((<| Ri2) y1 y2))))) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Ri1) x1 x2) ((|> Ri2) y1 y2)))))  
  
  data RightSpindle_ShelfTerm   : Set where 
      <|L : (RightSpindle_ShelfTerm → (RightSpindle_ShelfTerm → RightSpindle_ShelfTerm)) 
      |>L : (RightSpindle_ShelfTerm → (RightSpindle_ShelfTerm → RightSpindle_ShelfTerm))  
      
  data ClRightSpindle_ShelfTerm  (A : Set) : Set where 
      sing : (A → (ClRightSpindle_ShelfTerm A)) 
      <|Cl : ((ClRightSpindle_ShelfTerm A) → ((ClRightSpindle_ShelfTerm A) → (ClRightSpindle_ShelfTerm A))) 
      |>Cl : ((ClRightSpindle_ShelfTerm A) → ((ClRightSpindle_ShelfTerm A) → (ClRightSpindle_ShelfTerm A)))  
      
  data OpRightSpindle_ShelfTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightSpindle_ShelfTerm n)) 
      <|OL : ((OpRightSpindle_ShelfTerm n) → ((OpRightSpindle_ShelfTerm n) → (OpRightSpindle_ShelfTerm n))) 
      |>OL : ((OpRightSpindle_ShelfTerm n) → ((OpRightSpindle_ShelfTerm n) → (OpRightSpindle_ShelfTerm n)))  
      
  data OpRightSpindle_ShelfTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightSpindle_ShelfTerm2 n A)) 
      sing2 : (A → (OpRightSpindle_ShelfTerm2 n A)) 
      <|OL2 : ((OpRightSpindle_ShelfTerm2 n A) → ((OpRightSpindle_ShelfTerm2 n A) → (OpRightSpindle_ShelfTerm2 n A))) 
      |>OL2 : ((OpRightSpindle_ShelfTerm2 n A) → ((OpRightSpindle_ShelfTerm2 n A) → (OpRightSpindle_ShelfTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClRightSpindle_ShelfTerm A) → (ClRightSpindle_ShelfTerm A)) 
  simplifyCl _ (<|Cl x1 x2) = (<|Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (|>Cl x1 x2) = (|>Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpRightSpindle_ShelfTerm n) → (OpRightSpindle_ShelfTerm n)) 
  simplifyOpB _ (<|OL x1 x2) = (<|OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (|>OL x1 x2) = (|>OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpRightSpindle_ShelfTerm2 n A) → (OpRightSpindle_ShelfTerm2 n A)) 
  simplifyOp _ _ (<|OL2 x1 x2) = (<|OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (|>OL2 x1 x2) = (|>OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightSpindle_Shelf A) → (RightSpindle_ShelfTerm → A)) 
  evalB Ri (<|L x1 x2) = ((<| Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (|>L x1 x2) = ((|> Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightSpindle_Shelf A) → ((ClRightSpindle_ShelfTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (<|Cl x1 x2) = ((<| Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (|>Cl x1 x2) = ((|> Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((RightSpindle_Shelf A) → ((Vec A n) → ((OpRightSpindle_ShelfTerm n) → A))) 
  evalOpB n Ri vars (v x1) = (lookup vars x1)  
  evalOpB n Ri vars (<|OL x1 x2) = ((<| Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOpB n Ri vars (|>OL x1 x2) = ((|> Ri) (evalOpB n Ri vars x1) (evalOpB n Ri vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((RightSpindle_Shelf A) → ((Vec A n) → ((OpRightSpindle_ShelfTerm2 n A) → A))) 
  evalOp n Ri vars (v2 x1) = (lookup vars x1)  
  evalOp n Ri vars (sing2 x1) = x1  
  evalOp n Ri vars (<|OL2 x1 x2) = ((<| Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  evalOp n Ri vars (|>OL2 x1 x2) = ((|> Ri) (evalOp n Ri vars x1) (evalOp n Ri vars x2))  
  inductionB :  (P : (RightSpindle_ShelfTerm → Set)) →  (( (x1 x2 : RightSpindle_ShelfTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → (( (x1 x2 : RightSpindle_ShelfTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → ( (x : RightSpindle_ShelfTerm) → (P x)))) 
  inductionB p p<|l p|>l (<|L x1 x2) = (p<|l _ _ (inductionB p p<|l p|>l x1) (inductionB p p<|l p|>l x2))  
  inductionB p p<|l p|>l (|>L x1 x2) = (p|>l _ _ (inductionB p p<|l p|>l x1) (inductionB p p<|l p|>l x2))  
  inductionCl :  (A : Set) (P : ((ClRightSpindle_ShelfTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightSpindle_ShelfTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → (( (x1 x2 : (ClRightSpindle_ShelfTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → ( (x : (ClRightSpindle_ShelfTerm A)) → (P x))))) 
  inductionCl _ p psing p<|cl p|>cl (sing x1) = (psing x1)  
  inductionCl _ p psing p<|cl p|>cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl _ p psing p<|cl p|>cl x1) (inductionCl _ p psing p<|cl p|>cl x2))  
  inductionCl _ p psing p<|cl p|>cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl _ p psing p<|cl p|>cl x1) (inductionCl _ p psing p<|cl p|>cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpRightSpindle_ShelfTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightSpindle_ShelfTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → (( (x1 x2 : (OpRightSpindle_ShelfTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → ( (x : (OpRightSpindle_ShelfTerm n)) → (P x))))) 
  inductionOpB _ p pv p<|ol p|>ol (v x1) = (pv x1)  
  inductionOpB _ p pv p<|ol p|>ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB _ p pv p<|ol p|>ol x1) (inductionOpB _ p pv p<|ol p|>ol x2))  
  inductionOpB _ p pv p<|ol p|>ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB _ p pv p<|ol p|>ol x1) (inductionOpB _ p pv p<|ol p|>ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpRightSpindle_ShelfTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightSpindle_ShelfTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → (( (x1 x2 : (OpRightSpindle_ShelfTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → ( (x : (OpRightSpindle_ShelfTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 x1) (inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 x2))  
  inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 x1) (inductionOp _ _ p pv2 psing2 p<|ol2 p|>ol2 x2))  
  stageB :  (RightSpindle_ShelfTerm → (Staged RightSpindle_ShelfTerm))
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClRightSpindle_ShelfTerm A) → (Staged (ClRightSpindle_ShelfTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpRightSpindle_ShelfTerm n) → (Staged (OpRightSpindle_ShelfTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpRightSpindle_ShelfTerm2 n A) → (Staged (OpRightSpindle_ShelfTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      <|T : ((Repr A) → ((Repr A) → (Repr A))) 
      |>T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 