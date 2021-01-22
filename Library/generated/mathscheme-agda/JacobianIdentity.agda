
module JacobianIdentity   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record JacobianIdentity  (A : Set) : Set where 
     field  
      0ᵢ : A 
      + : (A → (A → A)) 
      * : (A → (A → A)) 
      jacobian_*_+ : ( {x y z : A} → (+ (+ (* x (* y z)) (* y (* z x))) (* z (* x y))) ≡ 0ᵢ)  
  
  open JacobianIdentity
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      +S : (AS → (AS → AS)) 
      *S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      jacobian_*_+P : ( {xP yP zP : (Prod A A)} → (+P (+P (*P xP (*P yP zP)) (*P yP (*P zP xP))) (*P zP (*P xP yP))) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ja1 : (JacobianIdentity A1)) (Ja2 : (JacobianIdentity A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Ja1)) ≡ (0ᵢ Ja2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ja1) x1 x2)) ≡ ((+ Ja2) (hom x1) (hom x2))) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ja1) x1 x2)) ≡ ((* Ja2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ja1 : (JacobianIdentity A1)) (Ja2 : (JacobianIdentity A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Ja1) (0ᵢ Ja2)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ja1) x1 x2) ((+ Ja2) y1 y2))))) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ja1) x1 x2) ((* Ja2) y1 y2)))))  
  
  data JacobianIdentityTerm   : Set where 
      0L : JacobianIdentityTerm 
      +L : (JacobianIdentityTerm → (JacobianIdentityTerm → JacobianIdentityTerm)) 
      *L : (JacobianIdentityTerm → (JacobianIdentityTerm → JacobianIdentityTerm))  
      
  data ClJacobianIdentityTerm  (A : Set) : Set where 
      sing : (A → (ClJacobianIdentityTerm A)) 
      0Cl : (ClJacobianIdentityTerm A) 
      +Cl : ((ClJacobianIdentityTerm A) → ((ClJacobianIdentityTerm A) → (ClJacobianIdentityTerm A))) 
      *Cl : ((ClJacobianIdentityTerm A) → ((ClJacobianIdentityTerm A) → (ClJacobianIdentityTerm A)))  
      
  data OpJacobianIdentityTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpJacobianIdentityTerm n)) 
      0OL : (OpJacobianIdentityTerm n) 
      +OL : ((OpJacobianIdentityTerm n) → ((OpJacobianIdentityTerm n) → (OpJacobianIdentityTerm n))) 
      *OL : ((OpJacobianIdentityTerm n) → ((OpJacobianIdentityTerm n) → (OpJacobianIdentityTerm n)))  
      
  data OpJacobianIdentityTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpJacobianIdentityTerm2 n A)) 
      sing2 : (A → (OpJacobianIdentityTerm2 n A)) 
      0OL2 : (OpJacobianIdentityTerm2 n A) 
      +OL2 : ((OpJacobianIdentityTerm2 n A) → ((OpJacobianIdentityTerm2 n A) → (OpJacobianIdentityTerm2 n A))) 
      *OL2 : ((OpJacobianIdentityTerm2 n A) → ((OpJacobianIdentityTerm2 n A) → (OpJacobianIdentityTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClJacobianIdentityTerm A) → (ClJacobianIdentityTerm A)) 
  simplifyCl 0Cl = 0Cl  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpJacobianIdentityTerm n) → (OpJacobianIdentityTerm n)) 
  simplifyOpB 0OL = 0OL  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpJacobianIdentityTerm2 n A) → (OpJacobianIdentityTerm2 n A)) 
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((JacobianIdentity A) → (JacobianIdentityTerm → A)) 
  evalB Ja 0L = (0ᵢ Ja)  
  evalB Ja (+L x1 x2) = ((+ Ja) (evalB Ja x1) (evalB Ja x2))  
  evalB Ja (*L x1 x2) = ((* Ja) (evalB Ja x1) (evalB Ja x2))  
  evalCl :  {A : Set} →  ((JacobianIdentity A) → ((ClJacobianIdentityTerm A) → A)) 
  evalCl Ja (sing x1) = x1  
  evalCl Ja 0Cl = (0ᵢ Ja)  
  evalCl Ja (+Cl x1 x2) = ((+ Ja) (evalCl Ja x1) (evalCl Ja x2))  
  evalCl Ja (*Cl x1 x2) = ((* Ja) (evalCl Ja x1) (evalCl Ja x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((JacobianIdentity A) → ((Vec A n) → ((OpJacobianIdentityTerm n) → A))) 
  evalOpB Ja vars (v x1) = (lookup vars x1)  
  evalOpB Ja vars 0OL = (0ᵢ Ja)  
  evalOpB Ja vars (+OL x1 x2) = ((+ Ja) (evalOpB Ja vars x1) (evalOpB Ja vars x2))  
  evalOpB Ja vars (*OL x1 x2) = ((* Ja) (evalOpB Ja vars x1) (evalOpB Ja vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((JacobianIdentity A) → ((Vec A n) → ((OpJacobianIdentityTerm2 n A) → A))) 
  evalOp Ja vars (v2 x1) = (lookup vars x1)  
  evalOp Ja vars (sing2 x1) = x1  
  evalOp Ja vars 0OL2 = (0ᵢ Ja)  
  evalOp Ja vars (+OL2 x1 x2) = ((+ Ja) (evalOp Ja vars x1) (evalOp Ja vars x2))  
  evalOp Ja vars (*OL2 x1 x2) = ((* Ja) (evalOp Ja vars x1) (evalOp Ja vars x2))  
  inductionB :  {P : (JacobianIdentityTerm → Set)} →  ((P 0L) → (( (x1 x2 : JacobianIdentityTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 x2 : JacobianIdentityTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → ( (x : JacobianIdentityTerm) → (P x))))) 
  inductionB p0l p+l p*l 0L = p0l  
  inductionB p0l p+l p*l (+L x1 x2) = (p+l _ _ (inductionB p0l p+l p*l x1) (inductionB p0l p+l p*l x2))  
  inductionB p0l p+l p*l (*L x1 x2) = (p*l _ _ (inductionB p0l p+l p*l x1) (inductionB p0l p+l p*l x2))  
  inductionCl :  {A : Set} {P : ((ClJacobianIdentityTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClJacobianIdentityTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 x2 : (ClJacobianIdentityTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → ( (x : (ClJacobianIdentityTerm A)) → (P x)))))) 
  inductionCl psing p0cl p+cl p*cl (sing x1) = (psing x1)  
  inductionCl psing p0cl p+cl p*cl 0Cl = p0cl  
  inductionCl psing p0cl p+cl p*cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p0cl p+cl p*cl x1) (inductionCl psing p0cl p+cl p*cl x2))  
  inductionCl psing p0cl p+cl p*cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p0cl p+cl p*cl x1) (inductionCl psing p0cl p+cl p*cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpJacobianIdentityTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpJacobianIdentityTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 x2 : (OpJacobianIdentityTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → ( (x : (OpJacobianIdentityTerm n)) → (P x)))))) 
  inductionOpB pv p0ol p+ol p*ol (v x1) = (pv x1)  
  inductionOpB pv p0ol p+ol p*ol 0OL = p0ol  
  inductionOpB pv p0ol p+ol p*ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p0ol p+ol p*ol x1) (inductionOpB pv p0ol p+ol p*ol x2))  
  inductionOpB pv p0ol p+ol p*ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p0ol p+ol p*ol x1) (inductionOpB pv p0ol p+ol p*ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpJacobianIdentityTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpJacobianIdentityTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 x2 : (OpJacobianIdentityTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → ( (x : (OpJacobianIdentityTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 x1) (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 x2))  
  inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 x1) (inductionOp pv2 psing2 p0ol2 p+ol2 p*ol2 x2))  
  stageB :  (JacobianIdentityTerm → (Staged JacobianIdentityTerm))
  stageB 0L = (Now 0L)  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClJacobianIdentityTerm A) → (Staged (ClJacobianIdentityTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpJacobianIdentityTerm n) → (Staged (OpJacobianIdentityTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpJacobianIdentityTerm2 n A) → (Staged (OpJacobianIdentityTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      *T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 