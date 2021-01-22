
module AntiCommutativeRing   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AntiCommutativeRing  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      neg : (A → A) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      1ᵢ : A 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ) 
      antiCommutative : ( {x y : A} → (* x y) ≡ (neg (* y x)))  
  
  open AntiCommutativeRing
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      0S : AS 
      negS : (AS → AS) 
      1S : AS  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      1P : (Prod A A) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (*P 0P xP) ≡ 0P) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (*P xP 0P) ≡ 0P) 
      antiCommutativeP : ( {xP yP : (Prod A A)} → (*P xP yP) ≡ (negP (*P yP xP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (An1 : (AntiCommutativeRing A1)) (An2 : (AntiCommutativeRing A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* An1) x1 x2)) ≡ ((* An2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ An1) x1 x2)) ≡ ((+ An2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ An1)) ≡ (0ᵢ An2) 
      pres-neg : ( {x1 : A1} → (hom ((neg An1) x1)) ≡ ((neg An2) (hom x1))) 
      pres-1 : (hom (1ᵢ An1)) ≡ (1ᵢ An2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (An1 : (AntiCommutativeRing A1)) (An2 : (AntiCommutativeRing A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* An1) x1 x2) ((* An2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ An1) x1 x2) ((+ An2) y1 y2))))) 
      interp-0 : (interp (0ᵢ An1) (0ᵢ An2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg An1) x1) ((neg An2) y1)))) 
      interp-1 : (interp (1ᵢ An1) (1ᵢ An2))  
  
  data AntiCommutativeRingTerm   : Set where 
      *L : (AntiCommutativeRingTerm → (AntiCommutativeRingTerm → AntiCommutativeRingTerm)) 
      +L : (AntiCommutativeRingTerm → (AntiCommutativeRingTerm → AntiCommutativeRingTerm)) 
      0L : AntiCommutativeRingTerm 
      negL : (AntiCommutativeRingTerm → AntiCommutativeRingTerm) 
      1L : AntiCommutativeRingTerm  
      
  data ClAntiCommutativeRingTerm  (A : Set) : Set where 
      sing : (A → (ClAntiCommutativeRingTerm A)) 
      *Cl : ((ClAntiCommutativeRingTerm A) → ((ClAntiCommutativeRingTerm A) → (ClAntiCommutativeRingTerm A))) 
      +Cl : ((ClAntiCommutativeRingTerm A) → ((ClAntiCommutativeRingTerm A) → (ClAntiCommutativeRingTerm A))) 
      0Cl : (ClAntiCommutativeRingTerm A) 
      negCl : ((ClAntiCommutativeRingTerm A) → (ClAntiCommutativeRingTerm A)) 
      1Cl : (ClAntiCommutativeRingTerm A)  
      
  data OpAntiCommutativeRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAntiCommutativeRingTerm n)) 
      *OL : ((OpAntiCommutativeRingTerm n) → ((OpAntiCommutativeRingTerm n) → (OpAntiCommutativeRingTerm n))) 
      +OL : ((OpAntiCommutativeRingTerm n) → ((OpAntiCommutativeRingTerm n) → (OpAntiCommutativeRingTerm n))) 
      0OL : (OpAntiCommutativeRingTerm n) 
      negOL : ((OpAntiCommutativeRingTerm n) → (OpAntiCommutativeRingTerm n)) 
      1OL : (OpAntiCommutativeRingTerm n)  
      
  data OpAntiCommutativeRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAntiCommutativeRingTerm2 n A)) 
      sing2 : (A → (OpAntiCommutativeRingTerm2 n A)) 
      *OL2 : ((OpAntiCommutativeRingTerm2 n A) → ((OpAntiCommutativeRingTerm2 n A) → (OpAntiCommutativeRingTerm2 n A))) 
      +OL2 : ((OpAntiCommutativeRingTerm2 n A) → ((OpAntiCommutativeRingTerm2 n A) → (OpAntiCommutativeRingTerm2 n A))) 
      0OL2 : (OpAntiCommutativeRingTerm2 n A) 
      negOL2 : ((OpAntiCommutativeRingTerm2 n A) → (OpAntiCommutativeRingTerm2 n A)) 
      1OL2 : (OpAntiCommutativeRingTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClAntiCommutativeRingTerm A) → (ClAntiCommutativeRingTerm A)) 
  simplifyCl (+Cl 0Cl x) = x  
  simplifyCl (+Cl x 0Cl) = x  
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (negCl (*Cl y x)) = (*Cl x y)  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 0Cl = 0Cl  
  simplifyCl (negCl x1) = (negCl (simplifyCl x1))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpAntiCommutativeRingTerm n) → (OpAntiCommutativeRingTerm n)) 
  simplifyOpB (+OL 0OL x) = x  
  simplifyOpB (+OL x 0OL) = x  
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (negOL (*OL y x)) = (*OL x y)  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 0OL = 0OL  
  simplifyOpB (negOL x1) = (negOL (simplifyOpB x1))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpAntiCommutativeRingTerm2 n A) → (OpAntiCommutativeRingTerm2 n A)) 
  simplifyOp (+OL2 0OL2 x) = x  
  simplifyOp (+OL2 x 0OL2) = x  
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (negOL2 (*OL2 y x)) = (*OL2 x y)  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (negOL2 x1) = (negOL2 (simplifyOp x1))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AntiCommutativeRing A) → (AntiCommutativeRingTerm → A)) 
  evalB An (*L x1 x2) = ((* An) (evalB An x1) (evalB An x2))  
  evalB An (+L x1 x2) = ((+ An) (evalB An x1) (evalB An x2))  
  evalB An 0L = (0ᵢ An)  
  evalB An (negL x1) = ((neg An) (evalB An x1))  
  evalB An 1L = (1ᵢ An)  
  evalCl :  {A : Set} →  ((AntiCommutativeRing A) → ((ClAntiCommutativeRingTerm A) → A)) 
  evalCl An (sing x1) = x1  
  evalCl An (*Cl x1 x2) = ((* An) (evalCl An x1) (evalCl An x2))  
  evalCl An (+Cl x1 x2) = ((+ An) (evalCl An x1) (evalCl An x2))  
  evalCl An 0Cl = (0ᵢ An)  
  evalCl An (negCl x1) = ((neg An) (evalCl An x1))  
  evalCl An 1Cl = (1ᵢ An)  
  evalOpB :  {A : Set} {n : Nat} →  ((AntiCommutativeRing A) → ((Vec A n) → ((OpAntiCommutativeRingTerm n) → A))) 
  evalOpB An vars (v x1) = (lookup vars x1)  
  evalOpB An vars (*OL x1 x2) = ((* An) (evalOpB An vars x1) (evalOpB An vars x2))  
  evalOpB An vars (+OL x1 x2) = ((+ An) (evalOpB An vars x1) (evalOpB An vars x2))  
  evalOpB An vars 0OL = (0ᵢ An)  
  evalOpB An vars (negOL x1) = ((neg An) (evalOpB An vars x1))  
  evalOpB An vars 1OL = (1ᵢ An)  
  evalOp :  {A : Set} {n : Nat} →  ((AntiCommutativeRing A) → ((Vec A n) → ((OpAntiCommutativeRingTerm2 n A) → A))) 
  evalOp An vars (v2 x1) = (lookup vars x1)  
  evalOp An vars (sing2 x1) = x1  
  evalOp An vars (*OL2 x1 x2) = ((* An) (evalOp An vars x1) (evalOp An vars x2))  
  evalOp An vars (+OL2 x1 x2) = ((+ An) (evalOp An vars x1) (evalOp An vars x2))  
  evalOp An vars 0OL2 = (0ᵢ An)  
  evalOp An vars (negOL2 x1) = ((neg An) (evalOp An vars x1))  
  evalOp An vars 1OL2 = (1ᵢ An)  
  inductionB :  {P : (AntiCommutativeRingTerm → Set)} →  (( (x1 x2 : AntiCommutativeRingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : AntiCommutativeRingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : AntiCommutativeRingTerm) → ((P x1) → (P (negL x1)))) → ((P 1L) → ( (x : AntiCommutativeRingTerm) → (P x))))))) 
  inductionB p*l p+l p0l pnegl p1l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l p0l pnegl p1l x1) (inductionB p*l p+l p0l pnegl p1l x2))  
  inductionB p*l p+l p0l pnegl p1l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l p0l pnegl p1l x1) (inductionB p*l p+l p0l pnegl p1l x2))  
  inductionB p*l p+l p0l pnegl p1l 0L = p0l  
  inductionB p*l p+l p0l pnegl p1l (negL x1) = (pnegl _ (inductionB p*l p+l p0l pnegl p1l x1))  
  inductionB p*l p+l p0l pnegl p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClAntiCommutativeRingTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAntiCommutativeRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClAntiCommutativeRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClAntiCommutativeRingTerm A)) → ((P x1) → (P (negCl x1)))) → ((P 1Cl) → ( (x : (ClAntiCommutativeRingTerm A)) → (P x)))))))) 
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x1) (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x2))  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x1) (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x2))  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl 0Cl = p0cl  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (negCl x1) = (pnegcl _ (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x1))  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpAntiCommutativeRingTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAntiCommutativeRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpAntiCommutativeRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpAntiCommutativeRingTerm n)) → ((P x1) → (P (negOL x1)))) → ((P 1OL) → ( (x : (OpAntiCommutativeRingTerm n)) → (P x)))))))) 
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x1) (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x2))  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x1) (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x2))  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol 0OL = p0ol  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (negOL x1) = (pnegol _ (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x1))  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpAntiCommutativeRingTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAntiCommutativeRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpAntiCommutativeRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpAntiCommutativeRingTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ((P 1OL2) → ( (x : (OpAntiCommutativeRingTerm2 n A)) → (P x))))))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (negOL2 x1) = (pnegol2 _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x1))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 1OL2 = p1ol2  
  stageB :  (AntiCommutativeRingTerm → (Staged AntiCommutativeRingTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClAntiCommutativeRingTerm A) → (Staged (ClAntiCommutativeRingTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpAntiCommutativeRingTerm n) → (Staged (OpAntiCommutativeRingTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpAntiCommutativeRingTerm2 n A) → (Staged (OpAntiCommutativeRingTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  stageOp 1OL2 = (Now 1OL2)  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A)) 
      1T : (Repr A)  
  
 