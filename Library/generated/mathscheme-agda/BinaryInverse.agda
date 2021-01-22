
module BinaryInverse   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BinaryInverse  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      <| : (A → (A → A)) 
      leftInverse : ( {x y : A} → (<| (|> x y) x) ≡ y) 
      rightInverse : ( {x y : A} → (|> x (<| y x)) ≡ y)  
  
  open BinaryInverse
  record Sig  (AS : Set) : Set where 
     field  
      |>S : (AS → (AS → AS)) 
      <|S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      <|P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftInverseP : ( {xP yP : (Prod A A)} → (<|P (|>P xP yP) xP) ≡ yP) 
      rightInverseP : ( {xP yP : (Prod A A)} → (|>P xP (<|P yP xP)) ≡ yP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Bi1 : (BinaryInverse A1)) (Bi2 : (BinaryInverse A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Bi1) x1 x2)) ≡ ((|> Bi2) (hom x1) (hom x2))) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Bi1) x1 x2)) ≡ ((<| Bi2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bi1 : (BinaryInverse A1)) (Bi2 : (BinaryInverse A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Bi1) x1 x2) ((|> Bi2) y1 y2))))) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Bi1) x1 x2) ((<| Bi2) y1 y2)))))  
  
  data BinaryInverseTerm   : Set where 
      |>L : (BinaryInverseTerm → (BinaryInverseTerm → BinaryInverseTerm)) 
      <|L : (BinaryInverseTerm → (BinaryInverseTerm → BinaryInverseTerm))  
      
  data ClBinaryInverseTerm  (A : Set) : Set where 
      sing : (A → (ClBinaryInverseTerm A)) 
      |>Cl : ((ClBinaryInverseTerm A) → ((ClBinaryInverseTerm A) → (ClBinaryInverseTerm A))) 
      <|Cl : ((ClBinaryInverseTerm A) → ((ClBinaryInverseTerm A) → (ClBinaryInverseTerm A)))  
      
  data OpBinaryInverseTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBinaryInverseTerm n)) 
      |>OL : ((OpBinaryInverseTerm n) → ((OpBinaryInverseTerm n) → (OpBinaryInverseTerm n))) 
      <|OL : ((OpBinaryInverseTerm n) → ((OpBinaryInverseTerm n) → (OpBinaryInverseTerm n)))  
      
  data OpBinaryInverseTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBinaryInverseTerm2 n A)) 
      sing2 : (A → (OpBinaryInverseTerm2 n A)) 
      |>OL2 : ((OpBinaryInverseTerm2 n A) → ((OpBinaryInverseTerm2 n A) → (OpBinaryInverseTerm2 n A))) 
      <|OL2 : ((OpBinaryInverseTerm2 n A) → ((OpBinaryInverseTerm2 n A) → (OpBinaryInverseTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClBinaryInverseTerm A) → (ClBinaryInverseTerm A)) 
  simplifyCl (|>Cl x1 x2) = (|>Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (<|Cl x1 x2) = (<|Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpBinaryInverseTerm n) → (OpBinaryInverseTerm n)) 
  simplifyOpB (|>OL x1 x2) = (|>OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (<|OL x1 x2) = (<|OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpBinaryInverseTerm2 n A) → (OpBinaryInverseTerm2 n A)) 
  simplifyOp (|>OL2 x1 x2) = (|>OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (<|OL2 x1 x2) = (<|OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BinaryInverse A) → (BinaryInverseTerm → A)) 
  evalB Bi (|>L x1 x2) = ((|> Bi) (evalB Bi x1) (evalB Bi x2))  
  evalB Bi (<|L x1 x2) = ((<| Bi) (evalB Bi x1) (evalB Bi x2))  
  evalCl :  {A : Set} →  ((BinaryInverse A) → ((ClBinaryInverseTerm A) → A)) 
  evalCl Bi (sing x1) = x1  
  evalCl Bi (|>Cl x1 x2) = ((|> Bi) (evalCl Bi x1) (evalCl Bi x2))  
  evalCl Bi (<|Cl x1 x2) = ((<| Bi) (evalCl Bi x1) (evalCl Bi x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((BinaryInverse A) → ((Vec A n) → ((OpBinaryInverseTerm n) → A))) 
  evalOpB Bi vars (v x1) = (lookup vars x1)  
  evalOpB Bi vars (|>OL x1 x2) = ((|> Bi) (evalOpB Bi vars x1) (evalOpB Bi vars x2))  
  evalOpB Bi vars (<|OL x1 x2) = ((<| Bi) (evalOpB Bi vars x1) (evalOpB Bi vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((BinaryInverse A) → ((Vec A n) → ((OpBinaryInverseTerm2 n A) → A))) 
  evalOp Bi vars (v2 x1) = (lookup vars x1)  
  evalOp Bi vars (sing2 x1) = x1  
  evalOp Bi vars (|>OL2 x1 x2) = ((|> Bi) (evalOp Bi vars x1) (evalOp Bi vars x2))  
  evalOp Bi vars (<|OL2 x1 x2) = ((<| Bi) (evalOp Bi vars x1) (evalOp Bi vars x2))  
  inductionB :  {P : (BinaryInverseTerm → Set)} →  (( (x1 x2 : BinaryInverseTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → (( (x1 x2 : BinaryInverseTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → ( (x : BinaryInverseTerm) → (P x)))) 
  inductionB p|>l p<|l (|>L x1 x2) = (p|>l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionB p|>l p<|l (<|L x1 x2) = (p<|l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionCl :  {A : Set} {P : ((ClBinaryInverseTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBinaryInverseTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → (( (x1 x2 : (ClBinaryInverseTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → ( (x : (ClBinaryInverseTerm A)) → (P x))))) 
  inductionCl psing p|>cl p<|cl (sing x1) = (psing x1)  
  inductionCl psing p|>cl p<|cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionCl psing p|>cl p<|cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpBinaryInverseTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBinaryInverseTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → (( (x1 x2 : (OpBinaryInverseTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → ( (x : (OpBinaryInverseTerm n)) → (P x))))) 
  inductionOpB pv p|>ol p<|ol (v x1) = (pv x1)  
  inductionOpB pv p|>ol p<|ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOpB pv p|>ol p<|ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpBinaryInverseTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBinaryInverseTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → (( (x1 x2 : (OpBinaryInverseTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → ( (x : (OpBinaryInverseTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  stageB :  (BinaryInverseTerm → (Staged BinaryInverseTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClBinaryInverseTerm A) → (Staged (ClBinaryInverseTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl x1) (stageCl x2))  
  stageCl (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpBinaryInverseTerm n) → (Staged (OpBinaryInverseTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpBinaryInverseTerm2 n A) → (Staged (OpBinaryInverseTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp x1) (stageOp x2))  
  stageOp (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A))) 
      <|T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 