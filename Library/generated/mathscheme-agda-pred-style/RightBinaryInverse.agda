
module RightBinaryInverse   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightBinaryInverse  (A : Set) (|> : (A → (A → A))) (<| : (A → (A → A))) : Set where 
     field  
      rightInverse : ( {x y : A} → (|> x (<| y x)) ≡ y)  
  
  record RightBinaryInverse  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      <| : (A → (A → A)) 
      isRightBinaryInverse : (IsRightBinaryInverse A |> <|)  
  
  open RightBinaryInverse
  record Sig  (AS : Set) : Set where 
     field  
      |>S : (AS → (AS → AS)) 
      <|S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      <|P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      rightInverseP : ( {xP yP : (Prod A A)} → (|>P xP (<|P yP xP)) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RightBinaryInverse A1)) (Ri2 : (RightBinaryInverse A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Ri1) x1 x2)) ≡ ((|> Ri2) (hom x1) (hom x2))) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Ri1) x1 x2)) ≡ ((<| Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RightBinaryInverse A1)) (Ri2 : (RightBinaryInverse A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Ri1) x1 x2) ((|> Ri2) y1 y2))))) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Ri1) x1 x2) ((<| Ri2) y1 y2)))))  
  
  data RightBinaryInverseTerm   : Set where 
      |>L : (RightBinaryInverseTerm → (RightBinaryInverseTerm → RightBinaryInverseTerm)) 
      <|L : (RightBinaryInverseTerm → (RightBinaryInverseTerm → RightBinaryInverseTerm))  
      
  data ClRightBinaryInverseTerm  (A : Set) : Set where 
      sing : (A → (ClRightBinaryInverseTerm A)) 
      |>Cl : ((ClRightBinaryInverseTerm A) → ((ClRightBinaryInverseTerm A) → (ClRightBinaryInverseTerm A))) 
      <|Cl : ((ClRightBinaryInverseTerm A) → ((ClRightBinaryInverseTerm A) → (ClRightBinaryInverseTerm A)))  
      
  data OpRightBinaryInverseTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRightBinaryInverseTerm n)) 
      |>OL : ((OpRightBinaryInverseTerm n) → ((OpRightBinaryInverseTerm n) → (OpRightBinaryInverseTerm n))) 
      <|OL : ((OpRightBinaryInverseTerm n) → ((OpRightBinaryInverseTerm n) → (OpRightBinaryInverseTerm n)))  
      
  data OpRightBinaryInverseTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRightBinaryInverseTerm2 n A)) 
      sing2 : (A → (OpRightBinaryInverseTerm2 n A)) 
      |>OL2 : ((OpRightBinaryInverseTerm2 n A) → ((OpRightBinaryInverseTerm2 n A) → (OpRightBinaryInverseTerm2 n A))) 
      <|OL2 : ((OpRightBinaryInverseTerm2 n A) → ((OpRightBinaryInverseTerm2 n A) → (OpRightBinaryInverseTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRightBinaryInverseTerm A) → (ClRightBinaryInverseTerm A)) 
  simplifyCl (|>Cl x1 x2) = (|>Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (<|Cl x1 x2) = (<|Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRightBinaryInverseTerm n) → (OpRightBinaryInverseTerm n)) 
  simplifyOpB (|>OL x1 x2) = (|>OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (<|OL x1 x2) = (<|OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRightBinaryInverseTerm2 n A) → (OpRightBinaryInverseTerm2 n A)) 
  simplifyOp (|>OL2 x1 x2) = (|>OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (<|OL2 x1 x2) = (<|OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RightBinaryInverse A) → (RightBinaryInverseTerm → A)) 
  evalB Ri (|>L x1 x2) = ((|> Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (<|L x1 x2) = ((<| Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RightBinaryInverse A) → ((ClRightBinaryInverseTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (|>Cl x1 x2) = ((|> Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (<|Cl x1 x2) = ((<| Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RightBinaryInverse A) → ((Vec A n) → ((OpRightBinaryInverseTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (|>OL x1 x2) = ((|> Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars (<|OL x1 x2) = ((<| Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RightBinaryInverse A) → ((Vec A n) → ((OpRightBinaryInverseTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (|>OL2 x1 x2) = ((|> Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars (<|OL2 x1 x2) = ((<| Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RightBinaryInverseTerm → Set)} →  (( (x1 x2 : RightBinaryInverseTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → (( (x1 x2 : RightBinaryInverseTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → ( (x : RightBinaryInverseTerm) → (P x)))) 
  inductionB p|>l p<|l (|>L x1 x2) = (p|>l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionB p|>l p<|l (<|L x1 x2) = (p<|l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionCl :  {A : Set} {P : ((ClRightBinaryInverseTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRightBinaryInverseTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → (( (x1 x2 : (ClRightBinaryInverseTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → ( (x : (ClRightBinaryInverseTerm A)) → (P x))))) 
  inductionCl psing p|>cl p<|cl (sing x1) = (psing x1)  
  inductionCl psing p|>cl p<|cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionCl psing p|>cl p<|cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRightBinaryInverseTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRightBinaryInverseTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → (( (x1 x2 : (OpRightBinaryInverseTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → ( (x : (OpRightBinaryInverseTerm n)) → (P x))))) 
  inductionOpB pv p|>ol p<|ol (v x1) = (pv x1)  
  inductionOpB pv p|>ol p<|ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOpB pv p|>ol p<|ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRightBinaryInverseTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRightBinaryInverseTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → (( (x1 x2 : (OpRightBinaryInverseTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → ( (x : (OpRightBinaryInverseTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  stageB :  (RightBinaryInverseTerm → (Staged RightBinaryInverseTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRightBinaryInverseTerm A) → (Staged (ClRightBinaryInverseTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl x1) (stageCl x2))  
  stageCl (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRightBinaryInverseTerm n) → (Staged (OpRightBinaryInverseTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRightBinaryInverseTerm2 n A) → (Staged (OpRightBinaryInverseTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp x1) (stageOp x2))  
  stageOp (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A))) 
      <|T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 