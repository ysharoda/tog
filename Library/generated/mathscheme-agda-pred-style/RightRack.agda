
module RightRack   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightRack  (A : Set) (<| : (A → (A → A))) (|> : (A → (A → A))) : Set where 
     field  
      rightDistributive : ( {x y z : A} → (<| (<| y z) x) ≡ (<| (<| y x) (<| z x)))  
  
  record RightRack  (A : Set) : Set where 
     field  
      <| : (A → (A → A)) 
      |> : (A → (A → A)) 
      isRightRack : (IsRightRack A <| |>)  
  
  open RightRack
  record Sig  (AS : Set) : Set where 
     field  
      <|S : (AS → (AS → AS)) 
      |>S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      <|P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightDistributiveP : ( {xP yP zP : (Prod A A)} → (<|P (<|P yP zP) xP) ≡ (<|P (<|P yP xP) (<|P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightRack A1)) (Ri2 : (RightRack A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Ri1) x1 x2)) ≡ ((<| Ri2) (hom x1) (hom x2))) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Ri1) x1 x2)) ≡ ((|> Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightRack A1)) (Ri2 : (RightRack A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Ri1) x1 x2) ((<| Ri2) y1 y2))))) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Ri1) x1 x2) ((|> Ri2) y1 y2)))))  
  
  data RightRackTerm   : Set where 
      <|L : (RightRackTerm → (RightRackTerm → RightRackTerm)) 
      |>L : (RightRackTerm → (RightRackTerm → RightRackTerm))  
      
  data ClRightRackTerm  (A : Set) : Set where 
      sing : (A → (ClRightRackTerm A)) 
      <|Cl : ((ClRightRackTerm A) → ((ClRightRackTerm A) → (ClRightRackTerm A))) 
      |>Cl : ((ClRightRackTerm A) → ((ClRightRackTerm A) → (ClRightRackTerm A)))  
      
  data OpRightRackTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightRackTerm n)) 
      <|OL : ((OpRightRackTerm n) → ((OpRightRackTerm n) → (OpRightRackTerm n))) 
      |>OL : ((OpRightRackTerm n) → ((OpRightRackTerm n) → (OpRightRackTerm n)))  
      
  data OpRightRackTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightRackTerm2 n A)) 
      sing2 : (A → (OpRightRackTerm2 n A)) 
      <|OL2 : ((OpRightRackTerm2 n A) → ((OpRightRackTerm2 n A) → (OpRightRackTerm2 n A))) 
      |>OL2 : ((OpRightRackTerm2 n A) → ((OpRightRackTerm2 n A) → (OpRightRackTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightRackTerm A) → (ClRightRackTerm A)) 
  simplifyCl (<|Cl x1 x2) = (<|Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (|>Cl x1 x2) = (|>Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightRackTerm n) → (OpRightRackTerm n)) 
  simplifyOpB (<|OL x1 x2) = (<|OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (|>OL x1 x2) = (|>OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightRackTerm2 n A) → (OpRightRackTerm2 n A)) 
  simplifyOp (<|OL2 x1 x2) = (<|OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (|>OL2 x1 x2) = (|>OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightRack A) → (RightRackTerm → A)) 
  evalB Ri (<|L x1 x2) = ((<| Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (|>L x1 x2) = ((|> Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightRack A) → ((ClRightRackTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (<|Cl x1 x2) = ((<| Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (|>Cl x1 x2) = ((|> Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightRack A) → ((Vec A n) → ((OpRightRackTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (<|OL x1 x2) = ((<| Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars (|>OL x1 x2) = ((|> Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightRack A) → ((Vec A n) → ((OpRightRackTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (<|OL2 x1 x2) = ((<| Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars (|>OL2 x1 x2) = ((|> Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightRackTerm → Set)} →  (( (x1 x2 : RightRackTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → (( (x1 x2 : RightRackTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → ( (x : RightRackTerm) → (P x)))) 
  inductionB p<|l p|>l (<|L x1 x2) = (p<|l _ _ (inductionB p<|l p|>l x1) (inductionB p<|l p|>l x2))  
  inductionB p<|l p|>l (|>L x1 x2) = (p|>l _ _ (inductionB p<|l p|>l x1) (inductionB p<|l p|>l x2))  
  inductionCl :  {A : Set} {P : ((ClRightRackTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightRackTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → (( (x1 x2 : (ClRightRackTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → ( (x : (ClRightRackTerm A)) → (P x))))) 
  inductionCl psing p<|cl p|>cl (sing x1) = (psing x1)  
  inductionCl psing p<|cl p|>cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl psing p<|cl p|>cl x1) (inductionCl psing p<|cl p|>cl x2))  
  inductionCl psing p<|cl p|>cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl psing p<|cl p|>cl x1) (inductionCl psing p<|cl p|>cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightRackTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightRackTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → (( (x1 x2 : (OpRightRackTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → ( (x : (OpRightRackTerm n)) → (P x))))) 
  inductionOpB pv p<|ol p|>ol (v x1) = (pv x1)  
  inductionOpB pv p<|ol p|>ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB pv p<|ol p|>ol x1) (inductionOpB pv p<|ol p|>ol x2))  
  inductionOpB pv p<|ol p|>ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB pv p<|ol p|>ol x1) (inductionOpB pv p<|ol p|>ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightRackTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightRackTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → (( (x1 x2 : (OpRightRackTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → ( (x : (OpRightRackTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p<|ol2 p|>ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p<|ol2 p|>ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p<|ol2 p|>ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp pv2 psing2 p<|ol2 p|>ol2 x1) (inductionOp pv2 psing2 p<|ol2 p|>ol2 x2))  
  inductionOp pv2 psing2 p<|ol2 p|>ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp pv2 psing2 p<|ol2 p|>ol2 x1) (inductionOp pv2 psing2 p<|ol2 p|>ol2 x2))  
  stageB :  (RightRackTerm → (Staged RightRackTerm))
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightRackTerm A) → (Staged (ClRightRackTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl x1) (stageCl x2))  
  stageCl (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightRackTerm n) → (Staged (OpRightRackTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightRackTerm2 n A) → (Staged (OpRightRackTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp x1) (stageOp x2))  
  stageOp (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      <|T : ((Repr A) → ((Repr A) → (Repr A))) 
      |>T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 