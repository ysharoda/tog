
module ModularLattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsModularLattice  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x) 
      leftAbsorp_*_+ : ( {x y : A} → (* x (+ x y)) ≡ x) 
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x) 
      leftModular_*_+ : ( {x y z : A} → (+ (* x y) (* x z)) ≡ (* x (+ y (* x z))))  
  
  record ModularLattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isModularLattice : (IsModularLattice A (*) (+))  
  
  open ModularLattice
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      idempotent_+P : ( {xP : (Prod A A)} → (+P xP xP) ≡ xP) 
      leftAbsorp_*_+P : ( {xP yP : (Prod A A)} → (*P xP (+P xP yP)) ≡ xP) 
      leftAbsorp_+_*P : ( {xP yP : (Prod A A)} → (+P xP (*P xP yP)) ≡ xP) 
      leftModular_*_+P : ( {xP yP zP : (Prod A A)} → (+P (*P xP yP) (*P xP zP)) ≡ (*P xP (+P yP (*P xP zP))))  
  
  record Hom  {A1 : Set} {A2 : Set} (Mo1 : (ModularLattice A1)) (Mo2 : (ModularLattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mo1) x1 x2)) ≡ ((* Mo2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Mo1) x1 x2)) ≡ ((+ Mo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mo1 : (ModularLattice A1)) (Mo2 : (ModularLattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mo1) x1 x2) ((* Mo2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Mo1) x1 x2) ((+ Mo2) y1 y2)))))  
  
  data ModularLatticeTerm   : Set where 
      *L : (ModularLatticeTerm → (ModularLatticeTerm → ModularLatticeTerm)) 
      +L : (ModularLatticeTerm → (ModularLatticeTerm → ModularLatticeTerm))  
      
  data ClModularLatticeTerm  (A : Set) : Set where 
      sing : (A → (ClModularLatticeTerm A)) 
      *Cl : ((ClModularLatticeTerm A) → ((ClModularLatticeTerm A) → (ClModularLatticeTerm A))) 
      +Cl : ((ClModularLatticeTerm A) → ((ClModularLatticeTerm A) → (ClModularLatticeTerm A)))  
      
  data OpModularLatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpModularLatticeTerm n)) 
      *OL : ((OpModularLatticeTerm n) → ((OpModularLatticeTerm n) → (OpModularLatticeTerm n))) 
      +OL : ((OpModularLatticeTerm n) → ((OpModularLatticeTerm n) → (OpModularLatticeTerm n)))  
      
  data OpModularLatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpModularLatticeTerm2 n A)) 
      sing2 : (A → (OpModularLatticeTerm2 n A)) 
      *OL2 : ((OpModularLatticeTerm2 n A) → ((OpModularLatticeTerm2 n A) → (OpModularLatticeTerm2 n A))) 
      +OL2 : ((OpModularLatticeTerm2 n A) → ((OpModularLatticeTerm2 n A) → (OpModularLatticeTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClModularLatticeTerm A) → (ClModularLatticeTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpModularLatticeTerm n) → (OpModularLatticeTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpModularLatticeTerm2 n A) → (OpModularLatticeTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((ModularLattice A) → (ModularLatticeTerm → A)) 
  evalB Mo (*L x1 x2) = ((* Mo) (evalB Mo x1) (evalB Mo x2))  
  evalB Mo (+L x1 x2) = ((+ Mo) (evalB Mo x1) (evalB Mo x2))  
  evalCl :  {A : Set} →  ((ModularLattice A) → ((ClModularLatticeTerm A) → A)) 
  evalCl Mo (sing x1) = x1  
  evalCl Mo (*Cl x1 x2) = ((* Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalCl Mo (+Cl x1 x2) = ((+ Mo) (evalCl Mo x1) (evalCl Mo x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((ModularLattice A) → ((Vec A n) → ((OpModularLatticeTerm n) → A))) 
  evalOpB n Mo vars (v x1) = (lookup vars x1)  
  evalOpB n Mo vars (*OL x1 x2) = ((* Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOpB n Mo vars (+OL x1 x2) = ((+ Mo) (evalOpB n Mo vars x1) (evalOpB n Mo vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((ModularLattice A) → ((Vec A n) → ((OpModularLatticeTerm2 n A) → A))) 
  evalOp n Mo vars (v2 x1) = (lookup vars x1)  
  evalOp n Mo vars (sing2 x1) = x1  
  evalOp n Mo vars (*OL2 x1 x2) = ((* Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  evalOp n Mo vars (+OL2 x1 x2) = ((+ Mo) (evalOp n Mo vars x1) (evalOp n Mo vars x2))  
  inductionB :  (P : (ModularLatticeTerm → Set)) →  (( (x1 x2 : ModularLatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : ModularLatticeTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : ModularLatticeTerm) → (P x)))) 
  inductionB p p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionB p p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClModularLatticeTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClModularLatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClModularLatticeTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClModularLatticeTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpModularLatticeTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpModularLatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpModularLatticeTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpModularLatticeTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOpB _ p pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpModularLatticeTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpModularLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpModularLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpModularLatticeTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (ModularLatticeTerm → (Staged ModularLatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClModularLatticeTerm A) → (Staged (ClModularLatticeTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpModularLatticeTerm n) → (Staged (OpModularLatticeTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpModularLatticeTerm2 n A) → (Staged (OpModularLatticeTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 