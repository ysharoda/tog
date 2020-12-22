
module IdempotentMultMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IdempotentMultMagma  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      idempotent_* : ( {x : A} → (* x x) ≡ x)  
  
  open IdempotentMultMagma
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Id1 : (IdempotentMultMagma A1)) (Id2 : (IdempotentMultMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Id1) x1 x2)) ≡ ((* Id2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Id1 : (IdempotentMultMagma A1)) (Id2 : (IdempotentMultMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Id1) x1 x2) ((* Id2) y1 y2)))))  
  
  data IdempotentMultMagmaTerm   : Set where 
      *L : (IdempotentMultMagmaTerm → (IdempotentMultMagmaTerm → IdempotentMultMagmaTerm))  
      
  data ClIdempotentMultMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClIdempotentMultMagmaTerm A)) 
      *Cl : ((ClIdempotentMultMagmaTerm A) → ((ClIdempotentMultMagmaTerm A) → (ClIdempotentMultMagmaTerm A)))  
      
  data OpIdempotentMultMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpIdempotentMultMagmaTerm n)) 
      *OL : ((OpIdempotentMultMagmaTerm n) → ((OpIdempotentMultMagmaTerm n) → (OpIdempotentMultMagmaTerm n)))  
      
  data OpIdempotentMultMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpIdempotentMultMagmaTerm2 n A)) 
      sing2 : (A → (OpIdempotentMultMagmaTerm2 n A)) 
      *OL2 : ((OpIdempotentMultMagmaTerm2 n A) → ((OpIdempotentMultMagmaTerm2 n A) → (OpIdempotentMultMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClIdempotentMultMagmaTerm A) → (ClIdempotentMultMagmaTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpIdempotentMultMagmaTerm n) → (OpIdempotentMultMagmaTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpIdempotentMultMagmaTerm2 n A) → (OpIdempotentMultMagmaTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((IdempotentMultMagma A) → (IdempotentMultMagmaTerm → A)) 
  evalB Id (*L x1 x2) = ((* Id) (evalB Id x1) (evalB Id x2))  
  evalCl :  {A : Set} →  ((IdempotentMultMagma A) → ((ClIdempotentMultMagmaTerm A) → A)) 
  evalCl Id (sing x1) = x1  
  evalCl Id (*Cl x1 x2) = ((* Id) (evalCl Id x1) (evalCl Id x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((IdempotentMultMagma A) → ((Vec A n) → ((OpIdempotentMultMagmaTerm n) → A))) 
  evalOpB n Id vars (v x1) = (lookup vars x1)  
  evalOpB n Id vars (*OL x1 x2) = ((* Id) (evalOpB n Id vars x1) (evalOpB n Id vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((IdempotentMultMagma A) → ((Vec A n) → ((OpIdempotentMultMagmaTerm2 n A) → A))) 
  evalOp n Id vars (v2 x1) = (lookup vars x1)  
  evalOp n Id vars (sing2 x1) = x1  
  evalOp n Id vars (*OL2 x1 x2) = ((* Id) (evalOp n Id vars x1) (evalOp n Id vars x2))  
  inductionB :  (P : (IdempotentMultMagmaTerm → Set)) →  (( (x1 x2 : IdempotentMultMagmaTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : IdempotentMultMagmaTerm) → (P x))) 
  inductionB p p*l (*L x1 x2) = (p*l _ _ (inductionB p p*l x1) (inductionB p p*l x2))  
  inductionCl :  (A : Set) (P : ((ClIdempotentMultMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClIdempotentMultMagmaTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClIdempotentMultMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl x1) (inductionCl _ p psing p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpIdempotentMultMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpIdempotentMultMagmaTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpIdempotentMultMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol x1) (inductionOpB _ p pv p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpIdempotentMultMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpIdempotentMultMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpIdempotentMultMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 x2))  
  stageB :  (IdempotentMultMagmaTerm → (Staged IdempotentMultMagmaTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClIdempotentMultMagmaTerm A) → (Staged (ClIdempotentMultMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpIdempotentMultMagmaTerm n) → (Staged (OpIdempotentMultMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpIdempotentMultMagmaTerm2 n A) → (Staged (OpIdempotentMultMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 