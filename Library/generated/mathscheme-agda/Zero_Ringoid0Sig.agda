
module Zero_Ringoid0Sig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Zero_Ringoid0Sig  (A : Set) : Set where 
     field  
      0ᵢ : A 
      * : (A → (A → A)) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ) 
      + : (A → (A → A))  
  
  open Zero_Ringoid0Sig
  record Sig  (AS : Set) : Set where 
     field  
      0S : AS 
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      0P : (Prod A A) 
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (*P 0P xP) ≡ 0P) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (*P xP 0P) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (Ze1 : (Zero_Ringoid0Sig A1)) (Ze2 : (Zero_Ringoid0Sig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0 : (hom (0ᵢ Ze1)) ≡ (0ᵢ Ze2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ze1) x1 x2)) ≡ ((* Ze2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ze1) x1 x2)) ≡ ((+ Ze2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ze1 : (Zero_Ringoid0Sig A1)) (Ze2 : (Zero_Ringoid0Sig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0 : (interp (0ᵢ Ze1) (0ᵢ Ze2)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ze1) x1 x2) ((* Ze2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ze1) x1 x2) ((+ Ze2) y1 y2)))))  
  
  data Zero_Ringoid0SigTerm   : Set where 
      0L : Zero_Ringoid0SigTerm 
      *L : (Zero_Ringoid0SigTerm → (Zero_Ringoid0SigTerm → Zero_Ringoid0SigTerm)) 
      +L : (Zero_Ringoid0SigTerm → (Zero_Ringoid0SigTerm → Zero_Ringoid0SigTerm))  
      
  data ClZero_Ringoid0SigTerm  (A : Set) : Set where 
      sing : (A → (ClZero_Ringoid0SigTerm A)) 
      0Cl : (ClZero_Ringoid0SigTerm A) 
      *Cl : ((ClZero_Ringoid0SigTerm A) → ((ClZero_Ringoid0SigTerm A) → (ClZero_Ringoid0SigTerm A))) 
      +Cl : ((ClZero_Ringoid0SigTerm A) → ((ClZero_Ringoid0SigTerm A) → (ClZero_Ringoid0SigTerm A)))  
      
  data OpZero_Ringoid0SigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpZero_Ringoid0SigTerm n)) 
      0OL : (OpZero_Ringoid0SigTerm n) 
      *OL : ((OpZero_Ringoid0SigTerm n) → ((OpZero_Ringoid0SigTerm n) → (OpZero_Ringoid0SigTerm n))) 
      +OL : ((OpZero_Ringoid0SigTerm n) → ((OpZero_Ringoid0SigTerm n) → (OpZero_Ringoid0SigTerm n)))  
      
  data OpZero_Ringoid0SigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpZero_Ringoid0SigTerm2 n A)) 
      sing2 : (A → (OpZero_Ringoid0SigTerm2 n A)) 
      0OL2 : (OpZero_Ringoid0SigTerm2 n A) 
      *OL2 : ((OpZero_Ringoid0SigTerm2 n A) → ((OpZero_Ringoid0SigTerm2 n A) → (OpZero_Ringoid0SigTerm2 n A))) 
      +OL2 : ((OpZero_Ringoid0SigTerm2 n A) → ((OpZero_Ringoid0SigTerm2 n A) → (OpZero_Ringoid0SigTerm2 n A)))  
      
  simplifyCl :  {A : Set} →  ((ClZero_Ringoid0SigTerm A) → (ClZero_Ringoid0SigTerm A)) 
  simplifyCl 0Cl = 0Cl  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpZero_Ringoid0SigTerm n) → (OpZero_Ringoid0SigTerm n)) 
  simplifyOpB 0OL = 0OL  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpZero_Ringoid0SigTerm2 n A) → (OpZero_Ringoid0SigTerm2 n A)) 
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Zero_Ringoid0Sig A) → (Zero_Ringoid0SigTerm → A)) 
  evalB Ze 0L = (0ᵢ Ze)  
  evalB Ze (*L x1 x2) = ((* Ze) (evalB Ze x1) (evalB Ze x2))  
  evalB Ze (+L x1 x2) = ((+ Ze) (evalB Ze x1) (evalB Ze x2))  
  evalCl :  {A : Set} →  ((Zero_Ringoid0Sig A) → ((ClZero_Ringoid0SigTerm A) → A)) 
  evalCl Ze (sing x1) = x1  
  evalCl Ze 0Cl = (0ᵢ Ze)  
  evalCl Ze (*Cl x1 x2) = ((* Ze) (evalCl Ze x1) (evalCl Ze x2))  
  evalCl Ze (+Cl x1 x2) = ((+ Ze) (evalCl Ze x1) (evalCl Ze x2))  
  evalOpB :  {A : Set} {n : Nat} →  ((Zero_Ringoid0Sig A) → ((Vec A n) → ((OpZero_Ringoid0SigTerm n) → A))) 
  evalOpB Ze vars (v x1) = (lookup vars x1)  
  evalOpB Ze vars 0OL = (0ᵢ Ze)  
  evalOpB Ze vars (*OL x1 x2) = ((* Ze) (evalOpB Ze vars x1) (evalOpB Ze vars x2))  
  evalOpB Ze vars (+OL x1 x2) = ((+ Ze) (evalOpB Ze vars x1) (evalOpB Ze vars x2))  
  evalOp :  {A : Set} {n : Nat} →  ((Zero_Ringoid0Sig A) → ((Vec A n) → ((OpZero_Ringoid0SigTerm2 n A) → A))) 
  evalOp Ze vars (v2 x1) = (lookup vars x1)  
  evalOp Ze vars (sing2 x1) = x1  
  evalOp Ze vars 0OL2 = (0ᵢ Ze)  
  evalOp Ze vars (*OL2 x1 x2) = ((* Ze) (evalOp Ze vars x1) (evalOp Ze vars x2))  
  evalOp Ze vars (+OL2 x1 x2) = ((+ Ze) (evalOp Ze vars x1) (evalOp Ze vars x2))  
  inductionB :  {P : (Zero_Ringoid0SigTerm → Set)} →  ((P 0L) → (( (x1 x2 : Zero_Ringoid0SigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : Zero_Ringoid0SigTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : Zero_Ringoid0SigTerm) → (P x))))) 
  inductionB p0l p*l p+l 0L = p0l  
  inductionB p0l p*l p+l (*L x1 x2) = (p*l _ _ (inductionB p0l p*l p+l x1) (inductionB p0l p*l p+l x2))  
  inductionB p0l p*l p+l (+L x1 x2) = (p+l _ _ (inductionB p0l p*l p+l x1) (inductionB p0l p*l p+l x2))  
  inductionCl :  {A : Set} {P : ((ClZero_Ringoid0SigTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0Cl) → (( (x1 x2 : (ClZero_Ringoid0SigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClZero_Ringoid0SigTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClZero_Ringoid0SigTerm A)) → (P x)))))) 
  inductionCl psing p0cl p*cl p+cl (sing x1) = (psing x1)  
  inductionCl psing p0cl p*cl p+cl 0Cl = p0cl  
  inductionCl psing p0cl p*cl p+cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p0cl p*cl p+cl x1) (inductionCl psing p0cl p*cl p+cl x2))  
  inductionCl psing p0cl p*cl p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p0cl p*cl p+cl x1) (inductionCl psing p0cl p*cl p+cl x2))  
  inductionOpB :  {n : Nat} {P : ((OpZero_Ringoid0SigTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0OL) → (( (x1 x2 : (OpZero_Ringoid0SigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpZero_Ringoid0SigTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpZero_Ringoid0SigTerm n)) → (P x)))))) 
  inductionOpB pv p0ol p*ol p+ol (v x1) = (pv x1)  
  inductionOpB pv p0ol p*ol p+ol 0OL = p0ol  
  inductionOpB pv p0ol p*ol p+ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p0ol p*ol p+ol x1) (inductionOpB pv p0ol p*ol p+ol x2))  
  inductionOpB pv p0ol p*ol p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p0ol p*ol p+ol x1) (inductionOpB pv p0ol p*ol p+ol x2))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpZero_Ringoid0SigTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0OL2) → (( (x1 x2 : (OpZero_Ringoid0SigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpZero_Ringoid0SigTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpZero_Ringoid0SigTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 x2))  
  inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 x1) (inductionOp pv2 psing2 p0ol2 p*ol2 p+ol2 x2))  
  stageB :  (Zero_Ringoid0SigTerm → (Staged Zero_Ringoid0SigTerm))
  stageB 0L = (Now 0L)  
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  {A : Set} →  ((ClZero_Ringoid0SigTerm A) → (Staged (ClZero_Ringoid0SigTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageOpB :  {n : Nat} →  ((OpZero_Ringoid0SigTerm n) → (Staged (OpZero_Ringoid0SigTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOp :  {n : Nat} {A : Set} →  ((OpZero_Ringoid0SigTerm2 n A) → (Staged (OpZero_Ringoid0SigTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0T : (Repr A) 
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 