
module DistributiveLattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record DistributiveLattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x) 
      leftAbsorp_*_+ : ( {x y : A} → (* x (+ x y)) ≡ x) 
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x) 
      leftModular_*_+ : ( {x y z : A} → (+ (* x y) (* x z)) ≡ (* x (+ y (* x z)))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z)))  
  
  open DistributiveLattice
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
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Di1 : (DistributiveLattice A1)) (Di2 : (DistributiveLattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Di1) x1 x2)) ≡ ((* Di2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Di1) x1 x2)) ≡ ((+ Di2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Di1 : (DistributiveLattice A1)) (Di2 : (DistributiveLattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Di1) x1 x2) ((* Di2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Di1) x1 x2) ((+ Di2) y1 y2)))))  
  
  data DistributiveLatticeTerm   : Set where 
      *L : (DistributiveLatticeTerm → (DistributiveLatticeTerm → DistributiveLatticeTerm)) 
      +L : (DistributiveLatticeTerm → (DistributiveLatticeTerm → DistributiveLatticeTerm))  
      
  data ClDistributiveLatticeTerm  (A : Set) : Set where 
      sing : (A → (ClDistributiveLatticeTerm A)) 
      *Cl : ((ClDistributiveLatticeTerm A) → ((ClDistributiveLatticeTerm A) → (ClDistributiveLatticeTerm A))) 
      +Cl : ((ClDistributiveLatticeTerm A) → ((ClDistributiveLatticeTerm A) → (ClDistributiveLatticeTerm A)))  
      
  data OpDistributiveLatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpDistributiveLatticeTerm n)) 
      *OL : ((OpDistributiveLatticeTerm n) → ((OpDistributiveLatticeTerm n) → (OpDistributiveLatticeTerm n))) 
      +OL : ((OpDistributiveLatticeTerm n) → ((OpDistributiveLatticeTerm n) → (OpDistributiveLatticeTerm n)))  
      
  data OpDistributiveLatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpDistributiveLatticeTerm2 n A)) 
      sing2 : (A → (OpDistributiveLatticeTerm2 n A)) 
      *OL2 : ((OpDistributiveLatticeTerm2 n A) → ((OpDistributiveLatticeTerm2 n A) → (OpDistributiveLatticeTerm2 n A))) 
      +OL2 : ((OpDistributiveLatticeTerm2 n A) → ((OpDistributiveLatticeTerm2 n A) → (OpDistributiveLatticeTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClDistributiveLatticeTerm A) → (ClDistributiveLatticeTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpDistributiveLatticeTerm n) → (OpDistributiveLatticeTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpDistributiveLatticeTerm2 n A) → (OpDistributiveLatticeTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((DistributiveLattice A) → (DistributiveLatticeTerm → A)) 
  evalB Di (*L x1 x2) = ((* Di) (evalB Di x1) (evalB Di x2))  
  evalB Di (+L x1 x2) = ((+ Di) (evalB Di x1) (evalB Di x2))  
  evalCl :  {A : Set} →  ((DistributiveLattice A) → ((ClDistributiveLatticeTerm A) → A)) 
  evalCl Di (sing x1) = x1  
  evalCl Di (*Cl x1 x2) = ((* Di) (evalCl Di x1) (evalCl Di x2))  
  evalCl Di (+Cl x1 x2) = ((+ Di) (evalCl Di x1) (evalCl Di x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((DistributiveLattice A) → ((Vec A n) → ((OpDistributiveLatticeTerm n) → A))) 
  evalOpB Di vars (v x1) = (lookup vars x1)  
  evalOpB Di vars (*OL x1 x2) = ((* Di) (evalOpB Di vars x1) (evalOpB Di vars x2))  
  evalOpB Di vars (+OL x1 x2) = ((+ Di) (evalOpB Di vars x1) (evalOpB Di vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((DistributiveLattice A) → ((Vec A n) → ((OpDistributiveLatticeTerm2 n A) → A))) 
  evalOp Di vars (v2 x1) = (lookup vars x1)  
  evalOp Di vars (sing2 x1) = x1  
  evalOp Di vars (*OL2 x1 x2) = ((* Di) (evalOp Di vars x1) (evalOp Di vars x2))  
  evalOp Di vars (+OL2 x1 x2) = ((+ Di) (evalOp Di vars x1) (evalOp Di vars x2))  
  inductionB :  {P : (DistributiveLatticeTerm → Set)} →  (( (x1 x2 : DistributiveLatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : DistributiveLatticeTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : DistributiveLatticeTerm) → (P x)))) 
  inductionB p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionB p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClDistributiveLatticeTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClDistributiveLatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClDistributiveLatticeTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClDistributiveLatticeTerm A)) → (P x))))) 
  inductionCl psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionCl psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpDistributiveLatticeTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpDistributiveLatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpDistributiveLatticeTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpDistributiveLatticeTerm n)) → (P x))))) 
  inductionOpB pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOpB pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpDistributiveLatticeTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpDistributiveLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpDistributiveLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpDistributiveLatticeTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (DistributiveLatticeTerm → (Staged DistributiveLatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClDistributiveLatticeTerm A) → (Staged (ClDistributiveLatticeTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpDistributiveLatticeTerm n) → (Staged (OpDistributiveLatticeTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpDistributiveLatticeTerm2 n A) → (Staged (OpDistributiveLatticeTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 