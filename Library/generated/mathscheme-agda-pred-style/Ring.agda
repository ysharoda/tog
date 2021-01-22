
module Ring   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRing  (A : Set) (* : (A → (A → A))) (+ : (A → (A → A))) (0ᵢ : A) (neg : (A → A)) (1ᵢ : A) : Set where 
     field  
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ)  
  
  record Ring  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      0ᵢ : A 
      neg : (A → A) 
      1ᵢ : A 
      isRing : (IsRing A (*) (+) 0ᵢ neg 1ᵢ)  
  
  open Ring
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
  
  record Hom  {A1 : Set} {A2 : Set} (Ri1 : (Ring A1)) (Ri2 : (Ring A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* Ri1) x1 x2)) ≡ ((* Ri2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Ri1) x1 x2)) ≡ ((+ Ri2) (hom x1) (hom x2))) 
      pres-0 : (hom (0ᵢ Ri1)) ≡ (0ᵢ Ri2) 
      pres-neg : ( {x1 : A1} → (hom ((neg Ri1) x1)) ≡ ((neg Ri2) (hom x1))) 
      pres-1 : (hom (1ᵢ Ri1)) ≡ (1ᵢ Ri2)  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Ri1 : (Ring A1)) (Ri2 : (Ring A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* Ri1) x1 x2) ((* Ri2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Ri1) x1 x2) ((+ Ri2) y1 y2))))) 
      interp-0 : (interp (0ᵢ Ri1) (0ᵢ Ri2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg Ri1) x1) ((neg Ri2) y1)))) 
      interp-1 : (interp (1ᵢ Ri1) (1ᵢ Ri2))  
  
  data RingTerm   : Set where 
      *L : (RingTerm → (RingTerm → RingTerm)) 
      +L : (RingTerm → (RingTerm → RingTerm)) 
      0L : RingTerm 
      negL : (RingTerm → RingTerm) 
      1L : RingTerm  
      
  data ClRingTerm  (A : Set) : Set where 
      sing : (A → (ClRingTerm A)) 
      *Cl : ((ClRingTerm A) → ((ClRingTerm A) → (ClRingTerm A))) 
      +Cl : ((ClRingTerm A) → ((ClRingTerm A) → (ClRingTerm A))) 
      0Cl : (ClRingTerm A) 
      negCl : ((ClRingTerm A) → (ClRingTerm A)) 
      1Cl : (ClRingTerm A)  
      
  data OpRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpRingTerm n)) 
      *OL : ((OpRingTerm n) → ((OpRingTerm n) → (OpRingTerm n))) 
      +OL : ((OpRingTerm n) → ((OpRingTerm n) → (OpRingTerm n))) 
      0OL : (OpRingTerm n) 
      negOL : ((OpRingTerm n) → (OpRingTerm n)) 
      1OL : (OpRingTerm n)  
      
  data OpRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpRingTerm2 n A)) 
      sing2 : (A → (OpRingTerm2 n A)) 
      *OL2 : ((OpRingTerm2 n A) → ((OpRingTerm2 n A) → (OpRingTerm2 n A))) 
      +OL2 : ((OpRingTerm2 n A) → ((OpRingTerm2 n A) → (OpRingTerm2 n A))) 
      0OL2 : (OpRingTerm2 n A) 
      negOL2 : ((OpRingTerm2 n A) → (OpRingTerm2 n A)) 
      1OL2 : (OpRingTerm2 n A)  
      
  simplifyCl :  {A : Set} →  ((ClRingTerm A) → (ClRingTerm A)) 
  simplifyCl (+Cl 0Cl x) = x  
  simplifyCl (+Cl x 0Cl) = x  
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 0Cl = 0Cl  
  simplifyCl (negCl x1) = (negCl (simplifyCl x1))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpRingTerm n) → (OpRingTerm n)) 
  simplifyOpB (+OL 0OL x) = x  
  simplifyOpB (+OL x 0OL) = x  
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 0OL = 0OL  
  simplifyOpB (negOL x1) = (negOL (simplifyOpB x1))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpRingTerm2 n A) → (OpRingTerm2 n A)) 
  simplifyOp (+OL2 0OL2 x) = x  
  simplifyOp (+OL2 x 0OL2) = x  
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (negOL2 x1) = (negOL2 (simplifyOp x1))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((Ring A) → (RingTerm → A)) 
  evalB Ri (*L x1 x2) = ((* Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri (+L x1 x2) = ((+ Ri) (evalB Ri x1) (evalB Ri x2))  
  evalB Ri 0L = (0ᵢ Ri)  
  evalB Ri (negL x1) = ((neg Ri) (evalB Ri x1))  
  evalB Ri 1L = (1ᵢ Ri)  
  evalCl :  {A : Set} →  ((Ring A) → ((ClRingTerm A) → A)) 
  evalCl Ri (sing x1) = x1  
  evalCl Ri (*Cl x1 x2) = ((* Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri (+Cl x1 x2) = ((+ Ri) (evalCl Ri x1) (evalCl Ri x2))  
  evalCl Ri 0Cl = (0ᵢ Ri)  
  evalCl Ri (negCl x1) = ((neg Ri) (evalCl Ri x1))  
  evalCl Ri 1Cl = (1ᵢ Ri)  
  evalOpB :  {A : Set} {n : Nat} →  ((Ring A) → ((Vec A n) → ((OpRingTerm n) → A))) 
  evalOpB Ri vars (v x1) = (lookup vars x1)  
  evalOpB Ri vars (*OL x1 x2) = ((* Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars (+OL x1 x2) = ((+ Ri) (evalOpB Ri vars x1) (evalOpB Ri vars x2))  
  evalOpB Ri vars 0OL = (0ᵢ Ri)  
  evalOpB Ri vars (negOL x1) = ((neg Ri) (evalOpB Ri vars x1))  
  evalOpB Ri vars 1OL = (1ᵢ Ri)  
  evalOp :  {A : Set} {n : Nat} →  ((Ring A) → ((Vec A n) → ((OpRingTerm2 n A) → A))) 
  evalOp Ri vars (v2 x1) = (lookup vars x1)  
  evalOp Ri vars (sing2 x1) = x1  
  evalOp Ri vars (*OL2 x1 x2) = ((* Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars (+OL2 x1 x2) = ((+ Ri) (evalOp Ri vars x1) (evalOp Ri vars x2))  
  evalOp Ri vars 0OL2 = (0ᵢ Ri)  
  evalOp Ri vars (negOL2 x1) = ((neg Ri) (evalOp Ri vars x1))  
  evalOp Ri vars 1OL2 = (1ᵢ Ri)  
  inductionB :  {P : (RingTerm → Set)} →  (( (x1 x2 : RingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : RingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 0L) → (( (x1 : RingTerm) → ((P x1) → (P (negL x1)))) → ((P 1L) → ( (x : RingTerm) → (P x))))))) 
  inductionB p*l p+l p0l pnegl p1l (*L x1 x2) = (p*l _ _ (inductionB p*l p+l p0l pnegl p1l x1) (inductionB p*l p+l p0l pnegl p1l x2))  
  inductionB p*l p+l p0l pnegl p1l (+L x1 x2) = (p+l _ _ (inductionB p*l p+l p0l pnegl p1l x1) (inductionB p*l p+l p0l pnegl p1l x2))  
  inductionB p*l p+l p0l pnegl p1l 0L = p0l  
  inductionB p*l p+l p0l pnegl p1l (negL x1) = (pnegl _ (inductionB p*l p+l p0l pnegl p1l x1))  
  inductionB p*l p+l p0l pnegl p1l 1L = p1l  
  inductionCl :  {A : Set} {P : ((ClRingTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 0Cl) → (( (x1 : (ClRingTerm A)) → ((P x1) → (P (negCl x1)))) → ((P 1Cl) → ( (x : (ClRingTerm A)) → (P x)))))))) 
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x1) (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x2))  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x1) (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x2))  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl 0Cl = p0cl  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl (negCl x1) = (pnegcl _ (inductionCl psing p*cl p+cl p0cl pnegcl p1cl x1))  
  inductionCl psing p*cl p+cl p0cl pnegcl p1cl 1Cl = p1cl  
  inductionOpB :  {n : Nat} {P : ((OpRingTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 0OL) → (( (x1 : (OpRingTerm n)) → ((P x1) → (P (negOL x1)))) → ((P 1OL) → ( (x : (OpRingTerm n)) → (P x)))))))) 
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x1) (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x2))  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x1) (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x2))  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol 0OL = p0ol  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol (negOL x1) = (pnegol _ (inductionOpB pv p*ol p+ol p0ol pnegol p1ol x1))  
  inductionOpB pv p*ol p+ol p0ol pnegol p1ol 1OL = p1ol  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpRingTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 0OL2) → (( (x1 : (OpRingTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ((P 1OL2) → ( (x : (OpRingTerm2 n A)) → (P x))))))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 (negOL2 x1) = (pnegol2 _ (inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 x1))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p0ol2 pnegol2 p1ol2 1OL2 = p1ol2  
  stageB :  (RingTerm → (Staged RingTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageB 1L = (Now 1L)  
  stageCl :  {A : Set} →  ((ClRingTerm A) → (Staged (ClRingTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  stageCl 1Cl = (Now 1Cl)  
  stageOpB :  {n : Nat} →  ((OpRingTerm n) → (Staged (OpRingTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  stageOpB 1OL = (Now 1OL)  
  stageOp :  {n : Nat} {A : Set} →  ((OpRingTerm2 n A) → (Staged (OpRingTerm2 n A))) 
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
  
 