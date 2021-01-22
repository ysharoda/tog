
module ShelfSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsShelfSig  (A : Set) (|> : (A → (A → A))) (<| : (A → (A → A))) : Set where 
    
  record ShelfSig  (A : Set) : Set where 
     field  
      |> : (A → (A → A)) 
      <| : (A → (A → A)) 
      isShelfSig : (IsShelfSig A |> <|)  
  
  open ShelfSig
  record Sig  (AS : Set) : Set where 
     field  
      |>S : (AS → (AS → AS)) 
      <|S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      |>P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      <|P : ((Prod A A) → ((Prod A A) → (Prod A A)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Sh1 : (ShelfSig A1)) (Sh2 : (ShelfSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-|> : ( {x1 x2 : A1} → (hom ((|> Sh1) x1 x2)) ≡ ((|> Sh2) (hom x1) (hom x2))) 
      pres-<| : ( {x1 x2 : A1} → (hom ((<| Sh1) x1 x2)) ≡ ((<| Sh2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Sh1 : (ShelfSig A1)) (Sh2 : (ShelfSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-|> : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((|> Sh1) x1 x2) ((|> Sh2) y1 y2))))) 
      interp-<| : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((<| Sh1) x1 x2) ((<| Sh2) y1 y2)))))  
  
  data ShelfSigTerm   : Set where 
      |>L : (ShelfSigTerm → (ShelfSigTerm → ShelfSigTerm)) 
      <|L : (ShelfSigTerm → (ShelfSigTerm → ShelfSigTerm))  
      
  data ClShelfSigTerm  (A : Set) : Set where 
      sing : (A → (ClShelfSigTerm A)) 
      |>Cl : ((ClShelfSigTerm A) → ((ClShelfSigTerm A) → (ClShelfSigTerm A))) 
      <|Cl : ((ClShelfSigTerm A) → ((ClShelfSigTerm A) → (ClShelfSigTerm A)))  
      
  data OpShelfSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpShelfSigTerm n)) 
      |>OL : ((OpShelfSigTerm n) → ((OpShelfSigTerm n) → (OpShelfSigTerm n))) 
      <|OL : ((OpShelfSigTerm n) → ((OpShelfSigTerm n) → (OpShelfSigTerm n)))  
      
  data OpShelfSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpShelfSigTerm2 n A)) 
      sing2 : (A → (OpShelfSigTerm2 n A)) 
      |>OL2 : ((OpShelfSigTerm2 n A) → ((OpShelfSigTerm2 n A) → (OpShelfSigTerm2 n A))) 
      <|OL2 : ((OpShelfSigTerm2 n A) → ((OpShelfSigTerm2 n A) → (OpShelfSigTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClShelfSigTerm A) → (ClShelfSigTerm A)) 
  simplifyCl (|>Cl x1 x2) = (|>Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (<|Cl x1 x2) = (<|Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpShelfSigTerm n) → (OpShelfSigTerm n)) 
  simplifyOpB (|>OL x1 x2) = (|>OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (<|OL x1 x2) = (<|OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpShelfSigTerm2 n A) → (OpShelfSigTerm2 n A)) 
  simplifyOp (|>OL2 x1 x2) = (|>OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (<|OL2 x1 x2) = (<|OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((ShelfSig A) → (ShelfSigTerm → A)) 
  evalB Sh (|>L x1 x2) = ((|> Sh) (evalB Sh x1) (evalB Sh x2))  
  evalB Sh (<|L x1 x2) = ((<| Sh) (evalB Sh x1) (evalB Sh x2))  
  evalCl :  {A : Set} →  ((ShelfSig A) → ((ClShelfSigTerm A) → A)) 
  evalCl Sh (sing x1) = x1  
  evalCl Sh (|>Cl x1 x2) = ((|> Sh) (evalCl Sh x1) (evalCl Sh x2))  
  evalCl Sh (<|Cl x1 x2) = ((<| Sh) (evalCl Sh x1) (evalCl Sh x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((ShelfSig A) → ((Vec A n) → ((OpShelfSigTerm n) → A))) 
  evalOpB Sh vars (v x1) = (lookup vars x1)  
  evalOpB Sh vars (|>OL x1 x2) = ((|> Sh) (evalOpB Sh vars x1) (evalOpB Sh vars x2))  
  evalOpB Sh vars (<|OL x1 x2) = ((<| Sh) (evalOpB Sh vars x1) (evalOpB Sh vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((ShelfSig A) → ((Vec A n) → ((OpShelfSigTerm2 n A) → A))) 
  evalOp Sh vars (v2 x1) = (lookup vars x1)  
  evalOp Sh vars (sing2 x1) = x1  
  evalOp Sh vars (|>OL2 x1 x2) = ((|> Sh) (evalOp Sh vars x1) (evalOp Sh vars x2))  
  evalOp Sh vars (<|OL2 x1 x2) = ((<| Sh) (evalOp Sh vars x1) (evalOp Sh vars x2))  
  inductionB :  {P : (ShelfSigTerm → Set)} →  (( (x1 x2 : ShelfSigTerm) → ((P x1) → ((P x2) → (P (|>L x1 x2))))) → (( (x1 x2 : ShelfSigTerm) → ((P x1) → ((P x2) → (P (<|L x1 x2))))) → ( (x : ShelfSigTerm) → (P x)))) 
  inductionB p|>l p<|l (|>L x1 x2) = (p|>l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionB p|>l p<|l (<|L x1 x2) = (p<|l _ _ (inductionB p|>l p<|l x1) (inductionB p|>l p<|l x2))  
  inductionCl :  {A : Set} {P : ((ClShelfSigTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClShelfSigTerm A)) → ((P x1) → ((P x2) → (P (|>Cl x1 x2))))) → (( (x1 x2 : (ClShelfSigTerm A)) → ((P x1) → ((P x2) → (P (<|Cl x1 x2))))) → ( (x : (ClShelfSigTerm A)) → (P x))))) 
  inductionCl psing p|>cl p<|cl (sing x1) = (psing x1)  
  inductionCl psing p|>cl p<|cl (|>Cl x1 x2) = (p|>cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionCl psing p|>cl p<|cl (<|Cl x1 x2) = (p<|cl _ _ (inductionCl psing p|>cl p<|cl x1) (inductionCl psing p|>cl p<|cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpShelfSigTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpShelfSigTerm n)) → ((P x1) → ((P x2) → (P (|>OL x1 x2))))) → (( (x1 x2 : (OpShelfSigTerm n)) → ((P x1) → ((P x2) → (P (<|OL x1 x2))))) → ( (x : (OpShelfSigTerm n)) → (P x))))) 
  inductionOpB pv p|>ol p<|ol (v x1) = (pv x1)  
  inductionOpB pv p|>ol p<|ol (|>OL x1 x2) = (p|>ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOpB pv p|>ol p<|ol (<|OL x1 x2) = (p<|ol _ _ (inductionOpB pv p|>ol p<|ol x1) (inductionOpB pv p|>ol p<|ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpShelfSigTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpShelfSigTerm2 n A)) → ((P x1) → ((P x2) → (P (|>OL2 x1 x2))))) → (( (x1 x2 : (OpShelfSigTerm2 n A)) → ((P x1) → ((P x2) → (P (<|OL2 x1 x2))))) → ( (x : (OpShelfSigTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (|>OL2 x1 x2) = (p|>ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  inductionOp pv2 psing2 p|>ol2 p<|ol2 (<|OL2 x1 x2) = (p<|ol2 _ _ (inductionOp pv2 psing2 p|>ol2 p<|ol2 x1) (inductionOp pv2 psing2 p|>ol2 p<|ol2 x2))  
  stageB :  (ShelfSigTerm → (Staged ShelfSigTerm))
  stageB (|>L x1 x2) = (stage2 |>L (codeLift2 |>L) (stageB x1) (stageB x2))  
  stageB (<|L x1 x2) = (stage2 <|L (codeLift2 <|L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClShelfSigTerm A) → (Staged (ClShelfSigTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (|>Cl x1 x2) = (stage2 |>Cl (codeLift2 |>Cl) (stageCl x1) (stageCl x2))  
  stageCl (<|Cl x1 x2) = (stage2 <|Cl (codeLift2 <|Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpShelfSigTerm n) → (Staged (OpShelfSigTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (|>OL x1 x2) = (stage2 |>OL (codeLift2 |>OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (<|OL x1 x2) = (stage2 <|OL (codeLift2 <|OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpShelfSigTerm2 n A) → (Staged (OpShelfSigTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (|>OL2 x1 x2) = (stage2 |>OL2 (codeLift2 |>OL2) (stageOp x1) (stageOp x2))  
  stageOp (<|OL2 x1 x2) = (stage2 <|OL2 (codeLift2 <|OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      |>T : ((Repr A) → ((Repr A) → (Repr A))) 
      <|T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 