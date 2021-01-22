
module Quandle   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsQuandle  (A : Set) (|> : (A → (A → A))) (<| : (A → (A → A))) : Set where 
     field  
      leftDistributive : ( {x y z : A} → (|> x (|> y z)) ≡ (|> (|> x y) (|> x z))) 
      rightDistributive : ( {x y z : A} → (<| (<| y z) x) ≡ (<| (<| y x) (<| z x))) 
      leftInverse : ( {x y : A} → (<| (|> x y) x) ≡ y) 
      rightInverse : ( {x y : A} → (|> x (<| y x)) ≡ y) 
      idempotent_|> : ( {x : A} → (|> x x) ≡ x) 
      idempotent_<| : ( {x : A} → (<| x x) ≡ x)  
  
  record Quandle  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      <| : (A → (A → A)) 
      isQuandle : (IsQuandle A |> <|)  
  
  open Quandle
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
      leftInverseP : ( {xP yP : (Prod A A)} → (<|P (|>P xP yP) xP) ≡ yP) 
      rightInverseP : ( {xP yP : (Prod A A)} → (|>P xP (<|P yP xP)) ≡ yP) 
      idempotent_|>P : ( {xP : (Prod A A)} → (|>P xP xP) ≡ xP) 
      idempotent_<|P : ( {xP : (Prod A A)} → (<|P xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Qu1 : (Quandle A1)) (Qu2 : (Quandle A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Qu1) x1 x2)) ≡ ((|> Qu2) (hom x1) (hom x2))) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Qu1) x1 x2)) ≡ ((<| Qu2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Qu1 : (Quandle A1)) (Qu2 : (Quandle A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Qu1) x1 x2) ((|> Qu2) y1 y2))))) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Qu1) x1 x2) ((<| Qu2) y1 y2)))))  
  
  data QuandleTerm   : Set where 
      |>L : (QuandleTerm → (QuandleTerm → QuandleTerm)) 
      <|L : (QuandleTerm → (QuandleTerm → QuandleTerm))  
      
  data ClQuandleTerm  (A : Set) : Set where 
      sing : (A → (ClQuandleTerm A)) 
      |>Cl : ((ClQuandleTerm A) → ((ClQuandleTerm A) → (ClQuandleTerm A))) 
      <|Cl : ((ClQuandleTerm A) → ((ClQuandleTerm A) → (ClQuandleTerm A)))  
      
  data OpQuandleTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpQuandleTerm n)) 
      |>OL : ((OpQuandleTerm n) → ((OpQuandleTerm n) → (OpQuandleTerm n))) 
      <|OL : ((OpQuandleTerm n) → ((OpQuandleTerm n) → (OpQuandleTerm n)))  
      
  data OpQuandleTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpQuandleTerm2 n A)) 
      sing2 : (A → (OpQuandleTerm2 n A)) 
      |>OL2 : ((OpQuandleTerm2 n A) → ((OpQuandleTerm2 n A) → (OpQuandleTerm2 n A))) 
      <|OL2 : ((OpQuandleTerm2 n A) → ((OpQuandleTerm2 n A) → (OpQuandleTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClQuandleTerm A) → (ClQuandleTerm A)) 
  simplifyCl (|>Cl x1 x2) = (|>Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (<|Cl x1 x2) = (<|Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpQuandleTerm n) → (OpQuandleTerm n)) 
  simplifyOpB (|>OL x1 x2) = (|>OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (<|OL x1 x2) = (<|OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpQuandleTerm2 n A) → (OpQuandleTerm2 n A)) 
  simplifyOp (|>OL2 x1 x2) = (|>OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (<|OL2 x1 x2) = (<|OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Quandle A) → (QuandleTerm → A)) 
  evalB Qu (|>L x1 x2) = ((|> Qu) (evalB Qu x1) (evalB Qu x2))  
  evalB Qu (<|L x1 x2) = ((<| Qu) (evalB Qu x1) (evalB Qu x2))  
  evalCl :  {A : Set} →  ((Quandle A) → ((ClQuandleTerm A) → A)) 
  evalCl Qu (sing x1) = x1  
  evalCl Qu (|>Cl x1 x2) = ((|> Qu) (evalCl Qu x1) (evalCl Qu x2))  
  evalCl Qu (<|Cl x1 x2) = ((<| Qu) (evalCl Qu x1) (evalCl Qu x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Quandle A) → ((Vec A n) → ((OpQuandleTerm n) → A))) 
  evalOpB Qu vars (v x1) = (lookup vars x1)  
  evalOpB Qu vars (|>OL x1 x2) = ((|> Qu) (evalOpB Qu vars x1) (evalOpB Qu vars x2))  
  evalOpB Qu vars (<|OL x1 x2) = ((<| Qu) (evalOpB Qu vars x1) (evalOpB Qu vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Quandle A) → ((Vec A n) → ((OpQuandleTerm2 n A) → A))) 
  evalOp Qu vars (v2 x1) = (lookup vars x1)  
  evalOp Qu vars (sing2 x1) = x1  
  evalOp Qu vars (|>OL2 x1 x2) = ((|> Qu) (evalOp Qu vars x1) (evalOp Qu vars x2))  
  evalOp Qu vars (<|OL2 x1 x2) = ((<| Qu) (evalOp Qu vars x1) (evalOp Qu vars x2))  
  inductionB :  {P : (QuandleTerm → Set)} →  (( (x1 x2 : QuandleTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → (( (x1 x2 : QuandleTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → ( (x : QuandleTerm) → (P x)))) 
  inductionB p|>l p<|l (|>L x1 x2) = (p|>l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionB p|>l p<|l (<|L x1 x2) = (p<|l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionCl :  {A : Set} {P : ((ClQuandleTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClQuandleTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → (( (x1 x2 : (ClQuandleTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → ( (x : (ClQuandleTerm A)) → (P x))))) 
  inductionCl psing p|>cl p<|cl (sing x1) = (psing x1)  
  inductionCl psing p|>cl p<|cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionCl psing p|>cl p<|cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpQuandleTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpQuandleTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → (( (x1 x2 : (OpQuandleTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → ( (x : (OpQuandleTerm n)) → (P x))))) 
  inductionOpB pv p|>ol p<|ol (v x1) = (pv x1)  
  inductionOpB pv p|>ol p<|ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOpB pv p|>ol p<|ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpQuandleTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpQuandleTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → (( (x1 x2 : (OpQuandleTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → ( (x : (OpQuandleTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  stageB :  (QuandleTerm → (Staged QuandleTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClQuandleTerm A) → (Staged (ClQuandleTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl x1) (stageCl x2))  
  stageCl (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpQuandleTerm n) → (Staged (OpQuandleTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpQuandleTerm2 n A) → (Staged (OpQuandleTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp x1) (stageOp x2))  
  stageOp (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A))) 
      <|T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 