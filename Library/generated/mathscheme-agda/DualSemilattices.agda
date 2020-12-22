
module DualSemilattices   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record DualSemilattices  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x)  
  
  open DualSemilattices
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
  
  record Hom  {A1 : Set} {A2 : Set} (Du1 : (DualSemilattices A1)) (Du2 : (DualSemilattices A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Du1) x1 x2)) ≡ ((* Du2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Du1) x1 x2)) ≡ ((+ Du2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Du1 : (DualSemilattices A1)) (Du2 : (DualSemilattices A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Du1) x1 x2) ((* Du2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Du1) x1 x2) ((+ Du2) y1 y2)))))  
  
  data DualSemilatticesTerm   : Set where 
      *L : (DualSemilatticesTerm → (DualSemilatticesTerm → DualSemilatticesTerm)) 
      +L : (DualSemilatticesTerm → (DualSemilatticesTerm → DualSemilatticesTerm))  
      
  data ClDualSemilatticesTerm  (A : Set) : Set where 
      sing : (A → (ClDualSemilatticesTerm A)) 
      *Cl : ((ClDualSemilatticesTerm A) → ((ClDualSemilatticesTerm A) → (ClDualSemilatticesTerm A))) 
      +Cl : ((ClDualSemilatticesTerm A) → ((ClDualSemilatticesTerm A) → (ClDualSemilatticesTerm A)))  
      
  data OpDualSemilatticesTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpDualSemilatticesTerm n)) 
      *OL : ((OpDualSemilatticesTerm n) → ((OpDualSemilatticesTerm n) → (OpDualSemilatticesTerm n))) 
      +OL : ((OpDualSemilatticesTerm n) → ((OpDualSemilatticesTerm n) → (OpDualSemilatticesTerm n)))  
      
  data OpDualSemilatticesTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpDualSemilatticesTerm2 n A)) 
      sing2 : (A → (OpDualSemilatticesTerm2 n A)) 
      *OL2 : ((OpDualSemilatticesTerm2 n A) → ((OpDualSemilatticesTerm2 n A) → (OpDualSemilatticesTerm2 n A))) 
      +OL2 : ((OpDualSemilatticesTerm2 n A) → ((OpDualSemilatticesTerm2 n A) → (OpDualSemilatticesTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClDualSemilatticesTerm A) → (ClDualSemilatticesTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpDualSemilatticesTerm n) → (OpDualSemilatticesTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpDualSemilatticesTerm2 n A) → (OpDualSemilatticesTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((DualSemilattices A) → (DualSemilatticesTerm → A)) 
  evalB Du (*L x1 x2) = ((* Du) (evalB Du x1) (evalB Du x2))  
  evalB Du (+L x1 x2) = ((+ Du) (evalB Du x1) (evalB Du x2))  
  evalCl :  {A : Set} →  ((DualSemilattices A) → ((ClDualSemilatticesTerm A) → A)) 
  evalCl Du (sing x1) = x1  
  evalCl Du (*Cl x1 x2) = ((* Du) (evalCl Du x1) (evalCl Du x2))  
  evalCl Du (+Cl x1 x2) = ((+ Du) (evalCl Du x1) (evalCl Du x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((DualSemilattices A) → ((Vec A n) → ((OpDualSemilatticesTerm n) → A))) 
  evalOpB n Du vars (v x1) = (lookup vars x1)  
  evalOpB n Du vars (*OL x1 x2) = ((* Du) (evalOpB n Du vars x1) (evalOpB n Du vars x2))  
  evalOpB n Du vars (+OL x1 x2) = ((+ Du) (evalOpB n Du vars x1) (evalOpB n Du vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((DualSemilattices A) → ((Vec A n) → ((OpDualSemilatticesTerm2 n A) → A))) 
  evalOp n Du vars (v2 x1) = (lookup vars x1)  
  evalOp n Du vars (sing2 x1) = x1  
  evalOp n Du vars (*OL2 x1 x2) = ((* Du) (evalOp n Du vars x1) (evalOp n Du vars x2))  
  evalOp n Du vars (+OL2 x1 x2) = ((+ Du) (evalOp n Du vars x1) (evalOp n Du vars x2))  
  inductionB :  (P : (DualSemilatticesTerm → Set)) →  (( (x1 x2 : DualSemilatticesTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : DualSemilatticesTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : DualSemilatticesTerm) → (P x)))) 
  inductionB p p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionB p p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l x1) (inductionB p p*l p+l x2))  
  inductionCl :  (A : Set) (P : ((ClDualSemilatticesTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClDualSemilatticesTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClDualSemilatticesTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClDualSemilatticesTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionCl _ p psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl x1) (inductionCl _ p psing p*cl p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpDualSemilatticesTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpDualSemilatticesTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpDualSemilatticesTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpDualSemilatticesTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOpB _ p pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol x1) (inductionOpB _ p pv p*ol p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpDualSemilatticesTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpDualSemilatticesTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpDualSemilatticesTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpDualSemilatticesTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (DualSemilatticesTerm → (Staged DualSemilatticesTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClDualSemilatticesTerm A) → (Staged (ClDualSemilatticesTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpDualSemilatticesTerm n) → (Staged (OpDualSemilatticesTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpDualSemilatticesTerm2 n A) → (Staged (OpDualSemilatticesTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 