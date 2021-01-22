
module PrimAdditiveGroup   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPrimAdditiveGroup  (A : Set) (0ᵢ_ : A) (*_ : (A → (A → A))) (inv_ : (A → A)) : Set where 
     field  
      lunit_0ᵢ_ : ( {x : A} → (*_ 0ᵢ_ x) ≡ x) 
      runit_0ᵢ_ : ( {x : A} → (*_ x 0ᵢ_) ≡ x) 
      associative_*_ : ( {x y z : A} → (*_ (*_ x y) z) ≡ (*_ x (*_ y z))) 
      leftInverse_inv_op_0ᵢ_ : ( {x : A} → (*_ x (inv_ x)) ≡ 0ᵢ_) 
      rightInverse_inv_op_0ᵢ_ : ( {x : A} → (*_ (inv_ x) x) ≡ 0ᵢ_) 
      commutative_*_ : ( {x y : A} → (*_ x y) ≡ (*_ y x))  
  
  record PrimAdditiveGroup  (A : Set) : Set where 
     field  
      0ᵢ_ : A 
      *_ : (A → (A → A)) 
      inv_ : (A → A) 
      isPrimAdditiveGroup : (IsPrimAdditiveGroup A 0ᵢ_ *_ inv_)  
  
  open PrimAdditiveGroup
  record Sig  (AS : Set) : Set where 
     field  
      0ᵢ_S : AS 
      *_S : (AS → (AS → AS)) 
      inv_S : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      0ᵢ_P : (Prod A A) 
      *_P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      inv_P : ((Prod A A) → (Prod A A)) 
      lunit_0ᵢ_P : ( {xP : (Prod A A)} → (*_P 0ᵢ_P xP) ≡ xP) 
      runit_0ᵢ_P : ( {xP : (Prod A A)} → (*_P xP 0ᵢ_P) ≡ xP) 
      associative_*_P : ( {xP yP zP : (Prod A A)} → (*_P (*_P xP yP) zP) ≡ (*_P xP (*_P yP zP))) 
      leftInverse_inv_op_0ᵢ_P : ( {xP : (Prod A A)} → (*_P xP (inv_P xP)) ≡ 0ᵢ_P) 
      rightInverse_inv_op_0ᵢ_P : ( {xP : (Prod A A)} → (*_P (inv_P xP) xP) ≡ 0ᵢ_P) 
      commutative_*_P : ( {xP yP : (Prod A A)} → (*_P xP yP) ≡ (*_P yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Pr1 : (PrimAdditiveGroup A1)) (Pr2 : (PrimAdditiveGroup A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-0_ : (hom (0ᵢ_ Pr1)) ≡ (0ᵢ_ Pr2) 
      pres-*_ : ( {x1 x2 : A1} → (hom ((*_ Pr1) x1 x2)) ≡ ((*_ Pr2) (hom x1) (hom x2))) 
      pres-inv_ : ( {x1 : A1} → (hom ((inv_ Pr1) x1)) ≡ ((inv_ Pr2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Pr1 : (PrimAdditiveGroup A1)) (Pr2 : (PrimAdditiveGroup A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-0_ : (interp (0ᵢ_ Pr1) (0ᵢ_ Pr2)) 
      interp-*_ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((*_ Pr1) x1 x2) ((*_ Pr2) y1 y2))))) 
      interp-inv_ : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((inv_ Pr1) x1) ((inv_ Pr2) y1))))  
  
  data PrimAdditiveGroupTerm   : Set where 
      0ᵢ_L : PrimAdditiveGroupTerm 
      *_L : (PrimAdditiveGroupTerm → (PrimAdditiveGroupTerm → PrimAdditiveGroupTerm)) 
      inv_L : (PrimAdditiveGroupTerm → PrimAdditiveGroupTerm)  
      
  data ClPrimAdditiveGroupTerm  (A : Set) : Set where 
      sing : (A → (ClPrimAdditiveGroupTerm A)) 
      0ᵢ_Cl : (ClPrimAdditiveGroupTerm A) 
      *_Cl : ((ClPrimAdditiveGroupTerm A) → ((ClPrimAdditiveGroupTerm A) → (ClPrimAdditiveGroupTerm A))) 
      inv_Cl : ((ClPrimAdditiveGroupTerm A) → (ClPrimAdditiveGroupTerm A))  
      
  data OpPrimAdditiveGroupTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpPrimAdditiveGroupTerm n)) 
      0ᵢ_OL : (OpPrimAdditiveGroupTerm n) 
      *_OL : ((OpPrimAdditiveGroupTerm n) → ((OpPrimAdditiveGroupTerm n) → (OpPrimAdditiveGroupTerm n))) 
      inv_OL : ((OpPrimAdditiveGroupTerm n) → (OpPrimAdditiveGroupTerm n))  
      
  data OpPrimAdditiveGroupTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpPrimAdditiveGroupTerm2 n A)) 
      sing2 : (A → (OpPrimAdditiveGroupTerm2 n A)) 
      0ᵢ_OL2 : (OpPrimAdditiveGroupTerm2 n A) 
      *_OL2 : ((OpPrimAdditiveGroupTerm2 n A) → ((OpPrimAdditiveGroupTerm2 n A) → (OpPrimAdditiveGroupTerm2 n A))) 
      inv_OL2 : ((OpPrimAdditiveGroupTerm2 n A) → (OpPrimAdditiveGroupTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClPrimAdditiveGroupTerm A) → (ClPrimAdditiveGroupTerm A)) 
  simplifyCl (*_Cl 0ᵢ_Cl x) = x  
  simplifyCl (*_Cl x 0ᵢ_Cl) = x  
  simplifyCl 0ᵢ_Cl = 0ᵢ_Cl  
  simplifyCl (*_Cl x1 x2) = (*_Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (inv_Cl x1) = (inv_Cl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpPrimAdditiveGroupTerm n) → (OpPrimAdditiveGroupTerm n)) 
  simplifyOpB (*_OL 0ᵢ_OL x) = x  
  simplifyOpB (*_OL x 0ᵢ_OL) = x  
  simplifyOpB 0ᵢ_OL = 0ᵢ_OL  
  simplifyOpB (*_OL x1 x2) = (*_OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (inv_OL x1) = (inv_OL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpPrimAdditiveGroupTerm2 n A) → (OpPrimAdditiveGroupTerm2 n A)) 
  simplifyOp (*_OL2 0ᵢ_OL2 x) = x  
  simplifyOp (*_OL2 x 0ᵢ_OL2) = x  
  simplifyOp 0ᵢ_OL2 = 0ᵢ_OL2  
  simplifyOp (*_OL2 x1 x2) = (*_OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (inv_OL2 x1) = (inv_OL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((PrimAdditiveGroup A) → (PrimAdditiveGroupTerm → A)) 
  evalB Pr 0ᵢ_L = (0ᵢ_ Pr)  
  evalB Pr (*_L x1 x2) = ((*_ Pr) (evalB Pr x1) (evalB Pr x2))  
  evalB Pr (inv_L x1) = ((inv_ Pr) (evalB Pr x1))  
  evalCl :  {A : Set} →  ((PrimAdditiveGroup A) → ((ClPrimAdditiveGroupTerm A) → A)) 
  evalCl Pr (sing x1) = x1  
  evalCl Pr 0ᵢ_Cl = (0ᵢ_ Pr)  
  evalCl Pr (*_Cl x1 x2) = ((*_ Pr) (evalCl Pr x1) (evalCl Pr x2))  
  evalCl Pr (inv_Cl x1) = ((inv_ Pr) (evalCl Pr x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((PrimAdditiveGroup A) → ((Vec A n) → ((OpPrimAdditiveGroupTerm n) → A))) 
  evalOpB Pr vars (v x1) = (lookup vars x1)  
  evalOpB Pr vars 0ᵢ_OL = (0ᵢ_ Pr)  
  evalOpB Pr vars (*_OL x1 x2) = ((*_ Pr) (evalOpB Pr vars x1) (evalOpB Pr vars x2))  
  evalOpB Pr vars (inv_OL x1) = ((inv_ Pr) (evalOpB Pr vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((PrimAdditiveGroup A) → ((Vec A n) → ((OpPrimAdditiveGroupTerm2 n A) → A))) 
  evalOp Pr vars (v2 x1) = (lookup vars x1)  
  evalOp Pr vars (sing2 x1) = x1  
  evalOp Pr vars 0ᵢ_OL2 = (0ᵢ_ Pr)  
  evalOp Pr vars (*_OL2 x1 x2) = ((*_ Pr) (evalOp Pr vars x1) (evalOp Pr vars x2))  
  evalOp Pr vars (inv_OL2 x1) = ((inv_ Pr) (evalOp Pr vars x1))  
  inductionB :  {P : (PrimAdditiveGroupTerm → Set)} →  ((P 0ᵢ_L) → (( (x1 x2 : PrimAdditiveGroupTerm) → ((P x1) → ((P x2) → (P (*_L x1 x2))))) → (( (x1 : PrimAdditiveGroupTerm) → ((P x1) → (P (inv_L x1)))) → ( (x : PrimAdditiveGroupTerm) → (P x))))) 
  inductionB p0_l p*_l pinv_l 0ᵢ_L = p0_l  
  inductionB p0_l p*_l pinv_l (*_L x1 x2) = (p*_l _ _ (inductionB p0_l p*_l pinv_l x1) (inductionB p0_l p*_l pinv_l x2))  
  inductionB p0_l p*_l pinv_l (inv_L x1) = (pinv_l _ (inductionB p0_l p*_l pinv_l x1))  
  inductionCl :  {A : Set} {P : ((ClPrimAdditiveGroupTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → ((P 0ᵢ_Cl) → (( (x1 x2 : (ClPrimAdditiveGroupTerm A)) → ((P x1) → ((P x2) → (P (*_Cl x1 x2))))) → (( (x1 : (ClPrimAdditiveGroupTerm A)) → ((P x1) → (P (inv_Cl x1)))) → ( (x : (ClPrimAdditiveGroupTerm A)) → (P x)))))) 
  inductionCl psing p0_cl p*_cl pinv_cl (sing x1) = (psing x1)  
  inductionCl psing p0_cl p*_cl pinv_cl 0ᵢ_Cl = p0_cl  
  inductionCl psing p0_cl p*_cl pinv_cl (*_Cl x1 x2) = (p*_cl _ _ (inductionCl psing p0_cl p*_cl pinv_cl x1) (inductionCl psing p0_cl p*_cl pinv_cl x2))  
  inductionCl psing p0_cl p*_cl pinv_cl (inv_Cl x1) = (pinv_cl _ (inductionCl psing p0_cl p*_cl pinv_cl x1))  
  inductionOpB :  {n : Nat} {P : ((OpPrimAdditiveGroupTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → ((P 0ᵢ_OL) → (( (x1 x2 : (OpPrimAdditiveGroupTerm n)) → ((P x1) → ((P x2) → (P (*_OL x1 x2))))) → (( (x1 : (OpPrimAdditiveGroupTerm n)) → ((P x1) → (P (inv_OL x1)))) → ( (x : (OpPrimAdditiveGroupTerm n)) → (P x)))))) 
  inductionOpB pv p0_ol p*_ol pinv_ol (v x1) = (pv x1)  
  inductionOpB pv p0_ol p*_ol pinv_ol 0ᵢ_OL = p0_ol  
  inductionOpB pv p0_ol p*_ol pinv_ol (*_OL x1 x2) = (p*_ol _ _ (inductionOpB pv p0_ol p*_ol pinv_ol x1) (inductionOpB pv p0_ol p*_ol pinv_ol x2))  
  inductionOpB pv p0_ol p*_ol pinv_ol (inv_OL x1) = (pinv_ol _ (inductionOpB pv p0_ol p*_ol pinv_ol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpPrimAdditiveGroupTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → ((P 0ᵢ_OL2) → (( (x1 x2 : (OpPrimAdditiveGroupTerm2 n A)) → ((P x1) → ((P x2) → (P (*_OL2 x1 x2))))) → (( (x1 : (OpPrimAdditiveGroupTerm2 n A)) → ((P x1) → (P (inv_OL2 x1)))) → ( (x : (OpPrimAdditiveGroupTerm2 n A)) → (P x))))))) 
  inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 0ᵢ_OL2 = p0_ol2  
  inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (*_OL2 x1 x2) = (p*_ol2 _ _ (inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 x1) (inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 x2))  
  inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (inv_OL2 x1) = (pinv_ol2 _ (inductionOp pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 x1))  
  stageB :  (PrimAdditiveGroupTerm → (Staged PrimAdditiveGroupTerm))
  stageB 0ᵢ_L = (Now 0ᵢ_L)  
  stageB (*_L x1 x2) = (stage2 *_L (codeLift2 *_L) (stageB x1) (stageB x2))  
  stageB (inv_L x1) = (stage1 inv_L (codeLift1 inv_L) (stageB x1))  
  stageCl :  {A : Set} →  ((ClPrimAdditiveGroupTerm A) → (Staged (ClPrimAdditiveGroupTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl 0ᵢ_Cl = (Now 0ᵢ_Cl)  
  stageCl (*_Cl x1 x2) = (stage2 *_Cl (codeLift2 *_Cl) (stageCl x1) (stageCl x2))  
  stageCl (inv_Cl x1) = (stage1 inv_Cl (codeLift1 inv_Cl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpPrimAdditiveGroupTerm n) → (Staged (OpPrimAdditiveGroupTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB 0ᵢ_OL = (Now 0ᵢ_OL)  
  stageOpB (*_OL x1 x2) = (stage2 *_OL (codeLift2 *_OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (inv_OL x1) = (stage1 inv_OL (codeLift1 inv_OL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpPrimAdditiveGroupTerm2 n A) → (Staged (OpPrimAdditiveGroupTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp 0ᵢ_OL2 = (Now 0ᵢ_OL2)  
  stageOp (*_OL2 x1 x2) = (stage2 *_OL2 (codeLift2 *_OL2) (stageOp x1) (stageOp x2))  
  stageOp (inv_OL2 x1) = (stage1 inv_OL2 (codeLift1 inv_OL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      0ᵢ_T : (Repr A) 
      *_T : ((Repr A) → ((Repr A) → (Repr A))) 
      inv_T : ((Repr A) → (Repr A))  
  
 