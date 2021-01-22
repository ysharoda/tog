
module RingoidWithMultAntiDistrib   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRingoidWithMultAntiDistrib  (A : Set) (* : (A → (A → A))) (prim : (A → A)) (+ : (A → (A → A))) : Set where 
     field  
      antidis_prim_* : ( {x y : A} → (prim (* x y)) ≡ (* (prim y) (prim x))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x)))  
  
  record RingoidWithMultAntiDistrib  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      prim : (A → A) 
      + : (A → (A → A)) 
      isRingoidWithMultAntiDistrib : (IsRingoidWithMultAntiDistrib A (*) prim (+))  
  
  open RingoidWithMultAntiDistrib
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      primS : (AS → AS) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      primP : ((Prod A A) → (Prod A A)) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      antidis_prim_*P : ( {xP yP : (Prod A A)} → (primP (*P xP yP)) ≡ (*P (primP yP) (primP xP))) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (RingoidWithMultAntiDistrib A1)) (Ri2 : (RingoidWithMultAntiDistrib A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ri1) x1 x2)) ≡ ((* Ri2) (hom x1) (hom x2))) 
      pres-prim : ( {x1 : A1} → (hom ((prim Ri1) x1)) ≡ ((prim Ri2) (hom x1))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ri1) x1 x2)) ≡ ((+ Ri2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (RingoidWithMultAntiDistrib A1)) (Ri2 : (RingoidWithMultAntiDistrib A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ri1) x1 x2) ((* Ri2) y1 y2))))) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim Ri1) x1) ((prim Ri2) y1)))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ri1) x1 x2) ((+ Ri2) y1 y2)))))  
  
  data RingoidWithMultAntiDistribTerm   : Set where 
      *L : (RingoidWithMultAntiDistribTerm → (RingoidWithMultAntiDistribTerm → RingoidWithMultAntiDistribTerm)) 
      primL : (RingoidWithMultAntiDistribTerm → RingoidWithMultAntiDistribTerm) 
      +L : (RingoidWithMultAntiDistribTerm → (RingoidWithMultAntiDistribTerm → RingoidWithMultAntiDistribTerm))  
      
  data ClRingoidWithMultAntiDistribTerm  (A : Set) : Set where 
      sing : (A → (ClRingoidWithMultAntiDistribTerm A)) 
      *Cl : ((ClRingoidWithMultAntiDistribTerm A) → ((ClRingoidWithMultAntiDistribTerm A) → (ClRingoidWithMultAntiDistribTerm A))) 
      primCl : ((ClRingoidWithMultAntiDistribTerm A) → (ClRingoidWithMultAntiDistribTerm A)) 
      +Cl : ((ClRingoidWithMultAntiDistribTerm A) → ((ClRingoidWithMultAntiDistribTerm A) → (ClRingoidWithMultAntiDistribTerm A)))  
      
  data OpRingoidWithMultAntiDistribTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRingoidWithMultAntiDistribTerm n)) 
      *OL : ((OpRingoidWithMultAntiDistribTerm n) → ((OpRingoidWithMultAntiDistribTerm n) → (OpRingoidWithMultAntiDistribTerm n))) 
      primOL : ((OpRingoidWithMultAntiDistribTerm n) → (OpRingoidWithMultAntiDistribTerm n)) 
      +OL : ((OpRingoidWithMultAntiDistribTerm n) → ((OpRingoidWithMultAntiDistribTerm n) → (OpRingoidWithMultAntiDistribTerm n)))  
      
  data OpRingoidWithMultAntiDistribTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRingoidWithMultAntiDistribTerm2 n A)) 
      sing2 : (A → (OpRingoidWithMultAntiDistribTerm2 n A)) 
      *OL2 : ((OpRingoidWithMultAntiDistribTerm2 n A) → ((OpRingoidWithMultAntiDistribTerm2 n A) → (OpRingoidWithMultAntiDistribTerm2 n A))) 
      primOL2 : ((OpRingoidWithMultAntiDistribTerm2 n A) → (OpRingoidWithMultAntiDistribTerm2 n A)) 
      +OL2 : ((OpRingoidWithMultAntiDistribTerm2 n A) → ((OpRingoidWithMultAntiDistribTerm2 n A) → (OpRingoidWithMultAntiDistribTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClRingoidWithMultAntiDistribTerm A) → (ClRingoidWithMultAntiDistribTerm A)) 
  simplifyCl (*Cl (primCl y) (primCl x)) = (primCl (*Cl x y))  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRingoidWithMultAntiDistribTerm n) → (OpRingoidWithMultAntiDistribTerm n)) 
  simplifyOpB (*OL (primOL y) (primOL x)) = (primOL (*OL x y))  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRingoidWithMultAntiDistribTerm2 n A) → (OpRingoidWithMultAntiDistribTerm2 n A)) 
  simplifyOp (*OL2 (primOL2 y) (primOL2 x)) = (primOL2 (*OL2 x y))  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((RingoidWithMultAntiDistrib A) → (RingoidWithMultAntiDistribTerm → A)) 
  evalB Ri (*L x1 x2) = ((* Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (primL x1) = ((prim Ri) (evalB Ri x1))  
  evalB Ri (+L x1 x2) = ((+ Ri) (evalB Ri x1) (evalB Ri x2))  
  evalCl :  {A : Set} →  ((RingoidWithMultAntiDistrib A) → ((ClRingoidWithMultAntiDistribTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (*Cl x1 x2) = ((* Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (primCl x1) = ((prim Ri) (evalCl Ri x1))  
  evalCl Ri (+Cl x1 x2) = ((+ Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((RingoidWithMultAntiDistrib A) → ((Vec A n) → ((OpRingoidWithMultAntiDistribTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (*OL x1 x2) = ((* Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars (primOL x1) = ((prim Ri) (evalOpB Ri vars x1))  
  evalOpB Ri vars (+OL x1 x2) = ((+ Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((RingoidWithMultAntiDistrib A) → ((Vec A n) → ((OpRingoidWithMultAntiDistribTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (*OL2 x1 x2) = ((* Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars (primOL2 x1) = ((prim Ri) (evalOp Ri vars x1))  
  evalOp Ri vars (+OL2 x1 x2) = ((+ Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  inductionB :  {P : (RingoidWithMultAntiDistribTerm → Set)} →  (( (x1 x2 : RingoidWithMultAntiDistribTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 : RingoidWithMultAntiDistribTerm) → ((P x1) → (P (primL x1)))) → (( (x1 x2 : RingoidWithMultAntiDistribTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : RingoidWithMultAntiDistribTerm) → (P x))))) 
  inductionB p*l ppriml p+l (*L x1 x2) = (p*l _ _ (inductionB p*l ppriml p+l x1) (inductionB p*l ppriml p+l x2))  
  inductionB p*l ppriml p+l (primL x1) = (ppriml _ (inductionB p*l ppriml p+l x1))  
  inductionB p*l ppriml p+l (+L x1 x2) = (p+l _ _ (inductionB p*l ppriml p+l x1) (inductionB p*l ppriml p+l x2))  
  inductionCl :  {A : Set} {P : ((ClRingoidWithMultAntiDistribTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRingoidWithMultAntiDistribTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 : (ClRingoidWithMultAntiDistribTerm A)) → ((P x1) → (P (primCl x1)))) → (( (x1 x2 : (ClRingoidWithMultAntiDistribTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClRingoidWithMultAntiDistribTerm A)) → (P x)))))) 
  inductionCl psing p*cl pprimcl p+cl (sing x1) = (psing x1)  
  inductionCl psing p*cl pprimcl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl pprimcl p+cl x1) (inductionCl psing p*cl pprimcl p+cl x2))  
  inductionCl psing p*cl pprimcl p+cl (primCl x1) = (pprimcl _ (inductionCl psing p*cl pprimcl p+cl x1))  
  inductionCl psing p*cl pprimcl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl pprimcl p+cl x1) (inductionCl psing p*cl pprimcl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpRingoidWithMultAntiDistribTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRingoidWithMultAntiDistribTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 : (OpRingoidWithMultAntiDistribTerm n)) → ((P x1) → (P (primOL x1)))) → (( (x1 x2 : (OpRingoidWithMultAntiDistribTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpRingoidWithMultAntiDistribTerm n)) → (P x)))))) 
  inductionOpB pv p*ol pprimol p+ol (v x1) = (pv x1)  
  inductionOpB pv p*ol pprimol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol pprimol p+ol x1) (inductionOpB pv p*ol pprimol p+ol x2))  
  inductionOpB pv p*ol pprimol p+ol (primOL x1) = (pprimol _ (inductionOpB pv p*ol pprimol p+ol x1))  
  inductionOpB pv p*ol pprimol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol pprimol p+ol x1) (inductionOpB pv p*ol pprimol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRingoidWithMultAntiDistribTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRingoidWithMultAntiDistribTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 : (OpRingoidWithMultAntiDistribTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → (( (x1 x2 : (OpRingoidWithMultAntiDistribTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpRingoidWithMultAntiDistribTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 x2))  
  inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 x1))  
  inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 x1) (inductionOp pv2 psing2 p*ol2 pprimol2 p+ol2 x2))  
  stageB :  (RingoidWithMultAntiDistribTerm → (Staged RingoidWithMultAntiDistribTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClRingoidWithMultAntiDistribTerm A) → (Staged (ClRingoidWithMultAntiDistribTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpRingoidWithMultAntiDistribTerm n) → (Staged (OpRingoidWithMultAntiDistribTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpRingoidWithMultAntiDistribTerm2 n A) → (Staged (OpRingoidWithMultAntiDistribTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      primT : ((Repr A) → (Repr A)) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 