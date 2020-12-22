
module Modularity   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsModularity  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      leftModular_*_+ : ( {x y z : A} → (+ (* x y) (* x z)) ≡ (* x (+ y (* x z))))  
  
  record Modularity  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isModularity : (IsModularity A (*) (+))  
  
  open Modularity
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftModular_*_+P : ( {xP yP zP : (Prod A A)} → (+P (*P xP yP) (*P xP zP)) ≡ (*P xP (+P yP (*P xP zP))))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (Modularity A1)) (Mo2 : (Modularity A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mo1) x1 x2)) ≡ ((* Mo2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Mo1) x1 x2)) ≡ ((+ Mo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (Modularity A1)) (Mo2 : (Modularity A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mo1) x1 x2) ((* Mo2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Mo1) x1 x2) ((+ Mo2) y1 y2)))))  
  
  data ModularityTerm   : Set where 
      *L : (ModularityTerm → (ModularityTerm → ModularityTerm)) 
      +L : (ModularityTerm → (ModularityTerm → ModularityTerm))  
      
  data ClModularityTerm  (A : Set) : Set where 
      sing : (A → (ClModularityTerm A)) 
      *Cl : ((ClModularityTerm A) → ((ClModularityTerm A) → (ClModularityTerm A))) 
      +Cl : ((ClModularityTerm A) → ((ClModularityTerm A) → (ClModularityTerm A)))  
      
  data OpModularityTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpModularityTerm n)) 
      *OL : ((OpModularityTerm n) → ((OpModularityTerm n) → (OpModularityTerm n))) 
      +OL : ((OpModularityTerm n) → ((OpModularityTerm n) → (OpModularityTerm n)))  
      
  data OpModularityTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpModularityTerm2 n A)) 
      sing2 : (A → (OpModularityTerm2 n A)) 
      *OL2 : ((OpModularityTerm2 n A) → ((OpModularityTerm2 n A) → (OpModularityTerm2 n A))) 
      +OL2 : ((OpModularityTerm2 n A) → ((OpModularityTerm2 n A) → (OpModularityTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClModularityTerm A) → (ClModularityTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpModularityTerm n) → (OpModularityTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpModularityTerm2 n A) → (OpModularityTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Modularity A) → (ModularityTerm → A)) 
  evalB Mo (*L x1 x2) = ((* Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo (+L x1 x2) = ((+ Mo) (evalB Mo x1) (evalB Mo x2))  
  evalCl :  {A : Set} →  ((Modularity A) → ((ClModularityTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (*Cl x1 x2) = ((* Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo (+Cl x1 x2) = ((+ Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((Modularity A) → ((Vec A n) → ((OpModularityTerm n) → A))) 
  evalOpB n Mo vars (v x1) = (lookup vars x1)  
  evalOpB n Mo vars (*OL x1 x2) = ((* Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOpB n Mo vars (+OL x1 x2) = ((+ Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((Modularity A) → ((Vec A n) → ((OpModularityTerm2 n A) → A))) 
  evalOp n Mo vars (v2 x1) = (lookup vars x1)  
  evalOp n Mo vars (sing2 x1) = x1  
  evalOp n Mo vars (*OL2 x1 x2) = ((* Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  evalOp n Mo vars (+OL2 x1 x2) = ((+ Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  inductionB :  (P : (ModularityTerm → Set)) →  (( (x1 x2 : ModularityTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : ModularityTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : ModularityTerm) → (P x)))) 
  inductionB p p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionB p p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClModularityTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClModularityTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClModularityTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClModularityTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpModularityTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpModularityTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpModularityTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpModularityTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOpB _ p pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpModularityTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpModularityTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpModularityTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpModularityTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (ModularityTerm → (Staged ModularityTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClModularityTerm A) → (Staged (ClModularityTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpModularityTerm n) → (Staged (OpModularityTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpModularityTerm2 n A) → (Staged (OpModularityTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 