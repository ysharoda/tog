
module Lattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsLattice  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) : Set where 
     field  
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x) 
      leftAbsorp_*_+ : ( {x y : A} → (* x (+ x y)) ≡ x) 
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x)  
  
  record Lattice  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      isLattice : (IsLattice A (*) (+))  
  
  open Lattice
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
  
  record Hom  {A1 : Set} {A2 : Set} (La1 : (Lattice A1)) (La2 : (Lattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* La1) x1 x2)) ≡ ((* La2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ La1) x1 x2)) ≡ ((+ La2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (La1 : (Lattice A1)) (La2 : (Lattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* La1) x1 x2) ((* La2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ La1) x1 x2) ((+ La2) y1 y2)))))  
  
  data LatticeTerm   : Set where 
      *L : (LatticeTerm → (LatticeTerm → LatticeTerm)) 
      +L : (LatticeTerm → (LatticeTerm → LatticeTerm))  
      
  data ClLatticeTerm  (A : Set) : Set where 
      sing : (A → (ClLatticeTerm A)) 
      *Cl : ((ClLatticeTerm A) → ((ClLatticeTerm A) → (ClLatticeTerm A))) 
      +Cl : ((ClLatticeTerm A) → ((ClLatticeTerm A) → (ClLatticeTerm A)))  
      
  data OpLatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpLatticeTerm n)) 
      *OL : ((OpLatticeTerm n) → ((OpLatticeTerm n) → (OpLatticeTerm n))) 
      +OL : ((OpLatticeTerm n) → ((OpLatticeTerm n) → (OpLatticeTerm n)))  
      
  data OpLatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpLatticeTerm2 n A)) 
      sing2 : (A → (OpLatticeTerm2 n A)) 
      *OL2 : ((OpLatticeTerm2 n A) → ((OpLatticeTerm2 n A) → (OpLatticeTerm2 n A))) 
      +OL2 : ((OpLatticeTerm2 n A) → ((OpLatticeTerm2 n A) → (OpLatticeTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClLatticeTerm A) → (ClLatticeTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpLatticeTerm n) → (OpLatticeTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpLatticeTerm2 n A) → (OpLatticeTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Lattice A) → (LatticeTerm → A)) 
  evalB La (*L x1 x2) = ((* La) (evalB La x1) (evalB La x2))  
  evalB La (+L x1 x2) = ((+ La) (evalB La x1) (evalB La x2))  
  evalCl :  {A : Set} →  ((Lattice A) → ((ClLatticeTerm A) → A)) 
  evalCl La (sing x1) = x1  
  evalCl La (*Cl x1 x2) = ((* La) (evalCl La x1) (evalCl La x2))  
  evalCl La (+Cl x1 x2) = ((+ La) (evalCl La x1) (evalCl La x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Lattice A) → ((Vec A n) → ((OpLatticeTerm n) → A))) 
  evalOpB La vars (v x1) = (lookup vars x1)  
  evalOpB La vars (*OL x1 x2) = ((* La) (evalOpB La vars x1) (evalOpB La vars x2))  
  evalOpB La vars (+OL x1 x2) = ((+ La) (evalOpB La vars x1) (evalOpB La vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Lattice A) → ((Vec A n) → ((OpLatticeTerm2 n A) → A))) 
  evalOp La vars (v2 x1) = (lookup vars x1)  
  evalOp La vars (sing2 x1) = x1  
  evalOp La vars (*OL2 x1 x2) = ((* La) (evalOp La vars x1) (evalOp La vars x2))  
  evalOp La vars (+OL2 x1 x2) = ((+ La) (evalOp La vars x1) (evalOp La vars x2))  
  inductionB :  {P : (LatticeTerm → Set)} →  (( (x1 x2 : LatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : LatticeTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : LatticeTerm) → (P x)))) 
  inductionB p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionB p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClLatticeTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClLatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClLatticeTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClLatticeTerm A)) → (P x))))) 
  inductionCl psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionCl psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpLatticeTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpLatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpLatticeTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpLatticeTerm n)) → (P x))))) 
  inductionOpB pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOpB pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpLatticeTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpLatticeTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (LatticeTerm → (Staged LatticeTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClLatticeTerm A) → (Staged (ClLatticeTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpLatticeTerm n) → (Staged (OpLatticeTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpLatticeTerm2 n A) → (Staged (OpLatticeTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 