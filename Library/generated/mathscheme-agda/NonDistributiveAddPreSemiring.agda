
module NonDistributiveAddPreSemiring   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record NonDistributiveAddPreSemiring  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      * : (A → (A → A))  
  
  open NonDistributiveAddPreSemiring
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS)) 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (No1 : (NonDistributiveAddPreSemiring A1)) (No2 : (NonDistributiveAddPreSemiring A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ No1) x1 x2)) ≡ ((+ No2) (hom x1) (hom x2))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* No1) x1 x2)) ≡ ((* No2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (No1 : (NonDistributiveAddPreSemiring A1)) (No2 : (NonDistributiveAddPreSemiring A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ No1) x1 x2) ((+ No2) y1 y2))))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* No1) x1 x2) ((* No2) y1 y2)))))  
  
  data NonDistributiveAddPreSemiringTerm   : Set where 
      +L : (NonDistributiveAddPreSemiringTerm → (NonDistributiveAddPreSemiringTerm → NonDistributiveAddPreSemiringTerm)) 
      *L : (NonDistributiveAddPreSemiringTerm → (NonDistributiveAddPreSemiringTerm → NonDistributiveAddPreSemiringTerm))  
      
  data ClNonDistributiveAddPreSemiringTerm  (A : Set) : Set where 
      sing : (A → (ClNonDistributiveAddPreSemiringTerm A)) 
      +Cl : ((ClNonDistributiveAddPreSemiringTerm A) → ((ClNonDistributiveAddPreSemiringTerm A) → (ClNonDistributiveAddPreSemiringTerm A))) 
      *Cl : ((ClNonDistributiveAddPreSemiringTerm A) → ((ClNonDistributiveAddPreSemiringTerm A) → (ClNonDistributiveAddPreSemiringTerm A)))  
      
  data OpNonDistributiveAddPreSemiringTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpNonDistributiveAddPreSemiringTerm n)) 
      +OL : ((OpNonDistributiveAddPreSemiringTerm n) → ((OpNonDistributiveAddPreSemiringTerm n) → (OpNonDistributiveAddPreSemiringTerm n))) 
      *OL : ((OpNonDistributiveAddPreSemiringTerm n) → ((OpNonDistributiveAddPreSemiringTerm n) → (OpNonDistributiveAddPreSemiringTerm n)))  
      
  data OpNonDistributiveAddPreSemiringTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpNonDistributiveAddPreSemiringTerm2 n A)) 
      sing2 : (A → (OpNonDistributiveAddPreSemiringTerm2 n A)) 
      +OL2 : ((OpNonDistributiveAddPreSemiringTerm2 n A) → ((OpNonDistributiveAddPreSemiringTerm2 n A) → (OpNonDistributiveAddPreSemiringTerm2 n A))) 
      *OL2 : ((OpNonDistributiveAddPreSemiringTerm2 n A) → ((OpNonDistributiveAddPreSemiringTerm2 n A) → (OpNonDistributiveAddPreSemiringTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClNonDistributiveAddPreSemiringTerm A) → (ClNonDistributiveAddPreSemiringTerm A)) 
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpNonDistributiveAddPreSemiringTerm n) → (OpNonDistributiveAddPreSemiringTerm n)) 
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpNonDistributiveAddPreSemiringTerm2 n A) → (OpNonDistributiveAddPreSemiringTerm2 n A)) 
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((NonDistributiveAddPreSemiring A) → (NonDistributiveAddPreSemiringTerm → A)) 
  evalB No (+L x1 x2) = ((+ No) (evalB No x1) (evalB No x2))  
  evalB No (*L x1 x2) = ((* No) (evalB No x1) (evalB No x2))  
  evalCl :  {A : Set} →  ((NonDistributiveAddPreSemiring A) → ((ClNonDistributiveAddPreSemiringTerm A) → A)) 
  evalCl No (sing x1) = x1  
  evalCl No (+Cl x1 x2) = ((+ No) (evalCl No x1) (evalCl No x2))  
  evalCl No (*Cl x1 x2) = ((* No) (evalCl No x1) (evalCl No x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((NonDistributiveAddPreSemiring A) → ((Vec A n) → ((OpNonDistributiveAddPreSemiringTerm n) → A))) 
  evalOpB n No vars (v x1) = (lookup vars x1)  
  evalOpB n No vars (+OL x1 x2) = ((+ No) (evalOpB n No vars x1) (evalOpB n No vars x2))  
  evalOpB n No vars (*OL x1 x2) = ((* No) (evalOpB n No vars x1) (evalOpB n No vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((NonDistributiveAddPreSemiring A) → ((Vec A n) → ((OpNonDistributiveAddPreSemiringTerm2 n A) → A))) 
  evalOp n No vars (v2 x1) = (lookup vars x1)  
  evalOp n No vars (sing2 x1) = x1  
  evalOp n No vars (+OL2 x1 x2) = ((+ No) (evalOp n No vars x1) (evalOp n No vars x2))  
  evalOp n No vars (*OL2 x1 x2) = ((* No) (evalOp n No vars x1) (evalOp n No vars x2))  
  inductionB :  (P : (NonDistributiveAddPreSemiringTerm → Set)) →  (( (x1 x2 : NonDistributiveAddPreSemiringTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 x2 : NonDistributiveAddPreSemiringTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : NonDistributiveAddPreSemiringTerm) → (P x)))) 
  inductionB p p+l p*l (+L x1 x2) = (p+l _ _ (inductionB p p+l p*l x1) (inductionB p p+l p*l x2))  
  inductionB p p+l p*l (*L x1 x2) = (p*l _ _ (inductionB p p+l p*l x1) (inductionB p p+l p*l x2))  
  inductionCl :  (A : Set) (P : ((ClNonDistributiveAddPreSemiringTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClNonDistributiveAddPreSemiringTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 x2 : (ClNonDistributiveAddPreSemiringTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClNonDistributiveAddPreSemiringTerm A)) → (P x))))) 
  inductionCl _ p psing p+cl p*cl (sing x1) = (psing x1)  
  inductionCl _ p psing p+cl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl p*cl x1) (inductionCl _ p psing p+cl p*cl x2))  
  inductionCl _ p psing p+cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p+cl p*cl x1) (inductionCl _ p psing p+cl p*cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpNonDistributiveAddPreSemiringTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpNonDistributiveAddPreSemiringTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 x2 : (OpNonDistributiveAddPreSemiringTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpNonDistributiveAddPreSemiringTerm n)) → (P x))))) 
  inductionOpB _ p pv p+ol p*ol (v x1) = (pv x1)  
  inductionOpB _ p pv p+ol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol p*ol x1) (inductionOpB _ p pv p+ol p*ol x2))  
  inductionOpB _ p pv p+ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p+ol p*ol x1) (inductionOpB _ p pv p+ol p*ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpNonDistributiveAddPreSemiringTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpNonDistributiveAddPreSemiringTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 x2 : (OpNonDistributiveAddPreSemiringTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpNonDistributiveAddPreSemiringTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 x2))  
  inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 p*ol2 x2))  
  stageB :  (NonDistributiveAddPreSemiringTerm → (Staged NonDistributiveAddPreSemiringTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClNonDistributiveAddPreSemiringTerm A) → (Staged (ClNonDistributiveAddPreSemiringTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpNonDistributiveAddPreSemiringTerm n) → (Staged (OpNonDistributiveAddPreSemiringTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpNonDistributiveAddPreSemiringTerm2 n A) → (Staged (OpNonDistributiveAddPreSemiringTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 