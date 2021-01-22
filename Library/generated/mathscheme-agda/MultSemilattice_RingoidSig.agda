
module MultSemilattice_RingoidSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MultSemilattice_RingoidSig  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      + : (A → (A → A))  
  
  open MultSemilattice_RingoidSig
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
  
  record Hom  {A1 : Set} {A2 : Set} (Mu1 : (MultSemilattice_RingoidSig A1)) (Mu2 : (MultSemilattice_RingoidSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Mu1) x1 x2)) ≡ ((* Mu2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Mu1) x1 x2)) ≡ ((+ Mu2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Mu1 : (MultSemilattice_RingoidSig A1)) (Mu2 : (MultSemilattice_RingoidSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Mu1) x1 x2) ((* Mu2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Mu1) x1 x2) ((+ Mu2) y1 y2)))))  
  
  data MultSemilattice_RingoidSigTerm   : Set where 
      *L : (MultSemilattice_RingoidSigTerm → (MultSemilattice_RingoidSigTerm → MultSemilattice_RingoidSigTerm)) 
      +L : (MultSemilattice_RingoidSigTerm → (MultSemilattice_RingoidSigTerm → MultSemilattice_RingoidSigTerm))  
      
  data ClMultSemilattice_RingoidSigTerm  (A : Set) : Set where 
      sing : (A → (ClMultSemilattice_RingoidSigTerm A)) 
      *Cl : ((ClMultSemilattice_RingoidSigTerm A) → ((ClMultSemilattice_RingoidSigTerm A) → (ClMultSemilattice_RingoidSigTerm A))) 
      +Cl : ((ClMultSemilattice_RingoidSigTerm A) → ((ClMultSemilattice_RingoidSigTerm A) → (ClMultSemilattice_RingoidSigTerm A)))  
      
  data OpMultSemilattice_RingoidSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpMultSemilattice_RingoidSigTerm n)) 
      *OL : ((OpMultSemilattice_RingoidSigTerm n) → ((OpMultSemilattice_RingoidSigTerm n) → (OpMultSemilattice_RingoidSigTerm n))) 
      +OL : ((OpMultSemilattice_RingoidSigTerm n) → ((OpMultSemilattice_RingoidSigTerm n) → (OpMultSemilattice_RingoidSigTerm n)))  
      
  data OpMultSemilattice_RingoidSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpMultSemilattice_RingoidSigTerm2 n A)) 
      sing2 : (A → (OpMultSemilattice_RingoidSigTerm2 n A)) 
      *OL2 : ((OpMultSemilattice_RingoidSigTerm2 n A) → ((OpMultSemilattice_RingoidSigTerm2 n A) → (OpMultSemilattice_RingoidSigTerm2 n A))) 
      +OL2 : ((OpMultSemilattice_RingoidSigTerm2 n A) → ((OpMultSemilattice_RingoidSigTerm2 n A) → (OpMultSemilattice_RingoidSigTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClMultSemilattice_RingoidSigTerm A) → (ClMultSemilattice_RingoidSigTerm A)) 
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpMultSemilattice_RingoidSigTerm n) → (OpMultSemilattice_RingoidSigTerm n)) 
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpMultSemilattice_RingoidSigTerm2 n A) → (OpMultSemilattice_RingoidSigTerm2 n A)) 
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((MultSemilattice_RingoidSig A) → (MultSemilattice_RingoidSigTerm → A)) 
  evalB Mu (*L x1 x2) = ((* Mu) (evalB Mu x1) (evalB Mu x2))  
  evalB Mu (+L x1 x2) = ((+ Mu) (evalB Mu x1) (evalB Mu x2))  
  evalCl :  {A : Set} →  ((MultSemilattice_RingoidSig A) → ((ClMultSemilattice_RingoidSigTerm A) → A)) 
  evalCl Mu (sing x1) = x1  
  evalCl Mu (*Cl x1 x2) = ((* Mu) (evalCl Mu x1) (evalCl Mu x2))  
  evalCl Mu (+Cl x1 x2) = ((+ Mu) (evalCl Mu x1) (evalCl Mu x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((MultSemilattice_RingoidSig A) → ((Vec A n) → ((OpMultSemilattice_RingoidSigTerm n) → A))) 
  evalOpB Mu vars (v x1) = (lookup vars x1)  
  evalOpB Mu vars (*OL x1 x2) = ((* Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  evalOpB Mu vars (+OL x1 x2) = ((+ Mu) (evalOpB Mu vars x1) (evalOpB Mu vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((MultSemilattice_RingoidSig A) → ((Vec A n) → ((OpMultSemilattice_RingoidSigTerm2 n A) → A))) 
  evalOp Mu vars (v2 x1) = (lookup vars x1)  
  evalOp Mu vars (sing2 x1) = x1  
  evalOp Mu vars (*OL2 x1 x2) = ((* Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  evalOp Mu vars (+OL2 x1 x2) = ((+ Mu) (evalOp Mu vars x1) (evalOp Mu vars x2))  
  inductionB :  {P : (MultSemilattice_RingoidSigTerm → Set)} →  (( (x1 x2 : MultSemilattice_RingoidSigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : MultSemilattice_RingoidSigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : MultSemilattice_RingoidSigTerm) → (P x)))) 
  inductionB p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionB p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l x1) (inductionB p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClMultSemilattice_RingoidSigTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClMultSemilattice_RingoidSigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClMultSemilattice_RingoidSigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClMultSemilattice_RingoidSigTerm A)) → (P x))))) 
  inductionCl psing p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionCl psing p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl x1) (inductionCl psing p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpMultSemilattice_RingoidSigTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpMultSemilattice_RingoidSigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpMultSemilattice_RingoidSigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpMultSemilattice_RingoidSigTerm n)) → (P x))))) 
  inductionOpB pv p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOpB pv p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol x1) (inductionOpB pv p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpMultSemilattice_RingoidSigTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpMultSemilattice_RingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpMultSemilattice_RingoidSigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpMultSemilattice_RingoidSigTerm2 n A)) → (P x)))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 x2))  
  stageB :  (MultSemilattice_RingoidSigTerm → (Staged MultSemilattice_RingoidSigTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClMultSemilattice_RingoidSigTerm A) → (Staged (ClMultSemilattice_RingoidSigTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpMultSemilattice_RingoidSigTerm n) → (Staged (OpMultSemilattice_RingoidSigTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpMultSemilattice_RingoidSigTerm2 n A) → (Staged (OpMultSemilattice_RingoidSigTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 