
module BoundedJoinLattice   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsBoundedJoinLattice  (A : Set) (+ : (A → (A → A))) (0ᵢ : A) (* : (A → (A → A))) : Set where 
     field  
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      idempotent_+ : ( {x : A} → (+ x x) ≡ x) 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      commutative_* : ( {x y : A} → (* x y) ≡ (* y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      idempotent_* : ( {x : A} → (* x x) ≡ x) 
      leftAbsorp_*_+ : ( {x y : A} → (* x (+ x y)) ≡ x) 
      leftAbsorp_+_* : ( {x y : A} → (+ x (* x y)) ≡ x)  
  
  record BoundedJoinLattice  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      0ᵢ : A 
      * : (A → (A → A)) 
      isBoundedJoinLattice : (IsBoundedJoinLattice A (+) 0ᵢ (*))  
  
  open BoundedJoinLattice
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS)) 
      0S : AS 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      idempotent_+P : ( {xP : (Prod A A)} → (+P xP xP) ≡ xP) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      commutative_*P : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (*P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      idempotent_*P : ( {xP : (Prod A A)} → (*P xP xP) ≡ xP) 
      leftAbsorp_*_+P : ( {xP yP : (Prod A A)} → (*P xP (+P xP yP)) ≡ xP) 
      leftAbsorp_+_*P : ( {xP yP : (Prod A A)} → (+P xP (*P xP yP)) ≡ xP)  
  
  record Hom  {A1 : Set} {A2 : Set} (Bo1 : (BoundedJoinLattice A1)) (Bo2 : (BoundedJoinLattice A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Bo1) x1 x2)) ≡ ((+ Bo2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Bo1)) ≡ (0ᵢ Bo2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Bo1) x1 x2)) ≡ ((* Bo2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Bo1 : (BoundedJoinLattice A1)) (Bo2 : (BoundedJoinLattice A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Bo1) x1 x2) ((+ Bo2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Bo1) (0ᵢ Bo2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Bo1) x1 x2) ((* Bo2) y1 y2)))))  
  
  data BoundedJoinLatticeTerm   : Set where 
      +L : (BoundedJoinLatticeTerm → (BoundedJoinLatticeTerm → BoundedJoinLatticeTerm)) 
      0L : BoundedJoinLatticeTerm 
      *L : (BoundedJoinLatticeTerm → (BoundedJoinLatticeTerm → BoundedJoinLatticeTerm))  
      
  data ClBoundedJoinLatticeTerm  (A : Set) : Set where 
      sing : (A → (ClBoundedJoinLatticeTerm A)) 
      +Cl : ((ClBoundedJoinLatticeTerm A) → ((ClBoundedJoinLatticeTerm A) → (ClBoundedJoinLatticeTerm A))) 
      0Cl : (ClBoundedJoinLatticeTerm A) 
      *Cl : ((ClBoundedJoinLatticeTerm A) → ((ClBoundedJoinLatticeTerm A) → (ClBoundedJoinLatticeTerm A)))  
      
  data OpBoundedJoinLatticeTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpBoundedJoinLatticeTerm n)) 
      +OL : ((OpBoundedJoinLatticeTerm n) → ((OpBoundedJoinLatticeTerm n) → (OpBoundedJoinLatticeTerm n))) 
      0OL : (OpBoundedJoinLatticeTerm n) 
      *OL : ((OpBoundedJoinLatticeTerm n) → ((OpBoundedJoinLatticeTerm n) → (OpBoundedJoinLatticeTerm n)))  
      
  data OpBoundedJoinLatticeTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpBoundedJoinLatticeTerm2 n A)) 
      sing2 : (A → (OpBoundedJoinLatticeTerm2 n A)) 
      +OL2 : ((OpBoundedJoinLatticeTerm2 n A) → ((OpBoundedJoinLatticeTerm2 n A) → (OpBoundedJoinLatticeTerm2 n A))) 
      0OL2 : (OpBoundedJoinLatticeTerm2 n A) 
      *OL2 : ((OpBoundedJoinLatticeTerm2 n A) → ((OpBoundedJoinLatticeTerm2 n A) → (OpBoundedJoinLatticeTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClBoundedJoinLatticeTerm A) → (ClBoundedJoinLatticeTerm A)) 
  simplifyCl (+Cl 0Cl x) = x  
  simplifyCl (+Cl x 0Cl) = x  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 0Cl = 0Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpBoundedJoinLatticeTerm n) → (OpBoundedJoinLatticeTerm n)) 
  simplifyOpB (+OL 0OL x) = x  
  simplifyOpB (+OL x 0OL) = x  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 0OL = 0OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpBoundedJoinLatticeTerm2 n A) → (OpBoundedJoinLatticeTerm2 n A)) 
  simplifyOp (+OL2 0OL2 x) = x  
  simplifyOp (+OL2 x 0OL2) = x  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((BoundedJoinLattice A) → (BoundedJoinLatticeTerm → A)) 
  evalB Bo (+L x1 x2) = ((+ Bo) (evalB Bo x1) (evalB Bo x2))  
  evalB Bo 0L = (0ᵢ Bo)  
  evalB Bo (*L x1 x2) = ((* Bo) (evalB Bo x1) (evalB Bo x2))  
  evalCl :  {A : Set} →  ((BoundedJoinLattice A) → ((ClBoundedJoinLatticeTerm A) → A)) 
  evalCl Bo (sing x1) = x1  
  evalCl Bo (+Cl x1 x2) = ((+ Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalCl Bo 0Cl = (0ᵢ Bo)  
  evalCl Bo (*Cl x1 x2) = ((* Bo) (evalCl Bo x1) (evalCl Bo x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((BoundedJoinLattice A) → ((Vec A n) → ((OpBoundedJoinLatticeTerm n) → A))) 
  evalOpB Bo vars (v x1) = (lookup vars x1)  
  evalOpB Bo vars (+OL x1 x2) = ((+ Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  evalOpB Bo vars 0OL = (0ᵢ Bo)  
  evalOpB Bo vars (*OL x1 x2) = ((* Bo) (evalOpB Bo vars x1) (evalOpB Bo vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((BoundedJoinLattice A) → ((Vec A n) → ((OpBoundedJoinLatticeTerm2 n A) → A))) 
  evalOp Bo vars (v2 x1) = (lookup vars x1)  
  evalOp Bo vars (sing2 x1) = x1  
  evalOp Bo vars (+OL2 x1 x2) = ((+ Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  evalOp Bo vars 0OL2 = (0ᵢ Bo)  
  evalOp Bo vars (*OL2 x1 x2) = ((* Bo) (evalOp Bo vars x1) (evalOp Bo vars x2))  
  inductionB :  {P : (BoundedJoinLatticeTerm → Set)} →  (( (x1 x2 : BoundedJoinLatticeTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 x2 : BoundedJoinLatticeTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : BoundedJoinLatticeTerm) → (P x))))) 
  inductionB p+l p0l p*l (+L x1 x2) = (p+l _ _ (inductionB p+l p0l p*l x1) (inductionB p+l p0l p*l x2))  
  inductionB p+l p0l p*l 0L = p0l  
  inductionB p+l p0l p*l (*L x1 x2) = (p*l _ _ (inductionB p+l p0l p*l x1) (inductionB p+l p0l p*l x2))  
  inductionCl :  {A : Set} {P : ((ClBoundedJoinLatticeTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClBoundedJoinLatticeTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 x2 : (ClBoundedJoinLatticeTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClBoundedJoinLatticeTerm A)) → (P x)))))) 
  inductionCl psing p+cl p0cl p*cl (sing x1) = (psing x1)  
  inductionCl psing p+cl p0cl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p+cl p0cl p*cl x1) (inductionCl psing p+cl p0cl p*cl x2))  
  inductionCl psing p+cl p0cl p*cl 0Cl = p0cl  
  inductionCl psing p+cl p0cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p+cl p0cl p*cl x1) (inductionCl psing p+cl p0cl p*cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpBoundedJoinLatticeTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpBoundedJoinLatticeTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 x2 : (OpBoundedJoinLatticeTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpBoundedJoinLatticeTerm n)) → (P x)))))) 
  inductionOpB pv p+ol p0ol p*ol (v x1) = (pv x1)  
  inductionOpB pv p+ol p0ol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p+ol p0ol p*ol x1) (inductionOpB pv p+ol p0ol p*ol x2))  
  inductionOpB pv p+ol p0ol p*ol 0OL = p0ol  
  inductionOpB pv p+ol p0ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p+ol p0ol p*ol x1) (inductionOpB pv p+ol p0ol p*ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpBoundedJoinLatticeTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpBoundedJoinLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 x2 : (OpBoundedJoinLatticeTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpBoundedJoinLatticeTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 x1) (inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 x2))  
  inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 x1) (inductionOp pv2 psing2 p+ol2 p0ol2 p*ol2 x2))  
  stageB :  (BoundedJoinLatticeTerm → (Staged BoundedJoinLatticeTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClBoundedJoinLatticeTerm A) → (Staged (ClBoundedJoinLatticeTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpBoundedJoinLatticeTerm n) → (Staged (OpBoundedJoinLatticeTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpBoundedJoinLatticeTerm2 n A) → (Staged (OpBoundedJoinLatticeTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 