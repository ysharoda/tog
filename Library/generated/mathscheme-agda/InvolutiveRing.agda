
module InvolutiveRing   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveRing  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      1ᵢ : A 
      leftDistributive_*_+ : ( {x y z : A} → (* x (+ y z)) ≡ (+ (* x y) (* x z))) 
      rightDistributive_*_+ : ( {x y z : A} → (* (+ y z) x) ≡ (+ (* y x) (* z x))) 
      prim : (A → A) 
      fixes_prim_1ᵢ : (prim 1ᵢ) ≡ 1ᵢ 
      involutive_prim : ( {x : A} → (prim (prim x)) ≡ x) 
      antidis_prim_+ : ( {x y : A} → (prim (+ x y)) ≡ (+ (prim y) (prim x))) 
      antidis_prim_* : ( {x y : A} → (prim (* x y)) ≡ (* (prim y) (prim x))) 
      0ᵢ : A 
      lunit_0ᵢ : ( {x : A} → (+ 0ᵢ x) ≡ x) 
      runit_0ᵢ : ( {x : A} → (+ x 0ᵢ) ≡ x) 
      associative_+ : ( {x y z : A} → (+ (+ x y) z) ≡ (+ x (+ y z))) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x)) 
      associative_* : ( {x y z : A} → (* (* x y) z) ≡ (* x (* y z))) 
      neg : (A → A) 
      leftInverse_inv_op_0ᵢ : ( {x : A} → (+ x (neg x)) ≡ 0ᵢ) 
      rightInverse_inv_op_0ᵢ : ( {x : A} → (+ (neg x) x) ≡ 0ᵢ) 
      lunit_1ᵢ : ( {x : A} → (* 1ᵢ x) ≡ x) 
      runit_1ᵢ : ( {x : A} → (* x 1ᵢ) ≡ x) 
      leftZero_op_0ᵢ : ( {x : A} → (* 0ᵢ x) ≡ 0ᵢ) 
      rightZero_op_0ᵢ : ( {x : A} → (* x 0ᵢ) ≡ 0ᵢ)  
  
  open InvolutiveRing
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      1S : AS 
      primS : (AS → AS) 
      0S : AS 
      negS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      1P : (Prod A A) 
      primP : ((Prod A A) → (Prod A A)) 
      0P : (Prod A A) 
      negP : ((Prod A A) → (Prod A A)) 
      leftDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P xP (+P yP zP)) ≡ (+P (*P xP yP) (*P xP zP))) 
      rightDistributive_*_+P : ( {xP yP zP : (Prod A A)} → (*P (+P yP zP) xP) ≡ (+P (*P yP xP) (*P zP xP))) 
      fixes_prim_1P : (primP 1P) ≡ 1P 
      involutive_primP : ( {xP : (Prod A A)} → (primP (primP xP)) ≡ xP) 
      antidis_prim_+P : ( {xP yP : (Prod A A)} → (primP (+P xP yP)) ≡ (+P (primP yP) (primP xP))) 
      antidis_prim_*P : ( {xP yP : (Prod A A)} → (primP (*P xP yP)) ≡ (*P (primP yP) (primP xP))) 
      lunit_0P : ( {xP : (Prod A A)} → (+P 0P xP) ≡ xP) 
      runit_0P : ( {xP : (Prod A A)} → (+P xP 0P) ≡ xP) 
      associative_+P : ( {xP yP zP : (Prod A A)} → (+P (+P xP yP) zP) ≡ (+P xP (+P yP zP))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP)) 
      associative_*P : ( {xP yP zP : (Prod A A)} → (*P (*P xP yP) zP) ≡ (*P xP (*P yP zP))) 
      leftInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P xP (negP xP)) ≡ 0P) 
      rightInverse_inv_op_0P : ( {xP : (Prod A A)} → (+P (negP xP) xP) ≡ 0P) 
      lunit_1P : ( {xP : (Prod A A)} → (*P 1P xP) ≡ xP) 
      runit_1P : ( {xP : (Prod A A)} → (*P xP 1P) ≡ xP) 
      leftZero_op_0P : ( {xP : (Prod A A)} → (*P 0P xP) ≡ 0P) 
      rightZero_op_0P : ( {xP : (Prod A A)} → (*P xP 0P) ≡ 0P)  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRing A1)) (In2 : (InvolutiveRing A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* In1) x1 x2)) ≡ ((* In2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ In1) x1 x2)) ≡ ((+ In2) (hom x1) (hom x2))) 
      pres-1 : (hom (1ᵢ In1)) ≡ (1ᵢ In2) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1))) 
      pres-0 : (hom (0ᵢ In1)) ≡ (0ᵢ In2) 
      pres-neg : ( {x1 : A1} → (hom ((neg In1) x1)) ≡ ((neg In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveRing A1)) (In2 : (InvolutiveRing A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* In1) x1 x2) ((* In2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ In1) x1 x2) ((+ In2) y1 y2))))) 
      interp-1 : (interp (1ᵢ In1) (1ᵢ In2)) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1)))) 
      interp-0 : (interp (0ᵢ In1) (0ᵢ In2)) 
      interp-neg : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((neg In1) x1) ((neg In2) y1))))  
  
  data InvolutiveRingTerm   : Set where 
      *L : (InvolutiveRingTerm → (InvolutiveRingTerm → InvolutiveRingTerm)) 
      +L : (InvolutiveRingTerm → (InvolutiveRingTerm → InvolutiveRingTerm)) 
      1L : InvolutiveRingTerm 
      primL : (InvolutiveRingTerm → InvolutiveRingTerm) 
      0L : InvolutiveRingTerm 
      negL : (InvolutiveRingTerm → InvolutiveRingTerm)  
      
  data ClInvolutiveRingTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveRingTerm A)) 
      *Cl : ((ClInvolutiveRingTerm A) → ((ClInvolutiveRingTerm A) → (ClInvolutiveRingTerm A))) 
      +Cl : ((ClInvolutiveRingTerm A) → ((ClInvolutiveRingTerm A) → (ClInvolutiveRingTerm A))) 
      1Cl : (ClInvolutiveRingTerm A) 
      primCl : ((ClInvolutiveRingTerm A) → (ClInvolutiveRingTerm A)) 
      0Cl : (ClInvolutiveRingTerm A) 
      negCl : ((ClInvolutiveRingTerm A) → (ClInvolutiveRingTerm A))  
      
  data OpInvolutiveRingTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveRingTerm n)) 
      *OL : ((OpInvolutiveRingTerm n) → ((OpInvolutiveRingTerm n) → (OpInvolutiveRingTerm n))) 
      +OL : ((OpInvolutiveRingTerm n) → ((OpInvolutiveRingTerm n) → (OpInvolutiveRingTerm n))) 
      1OL : (OpInvolutiveRingTerm n) 
      primOL : ((OpInvolutiveRingTerm n) → (OpInvolutiveRingTerm n)) 
      0OL : (OpInvolutiveRingTerm n) 
      negOL : ((OpInvolutiveRingTerm n) → (OpInvolutiveRingTerm n))  
      
  data OpInvolutiveRingTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveRingTerm2 n A)) 
      sing2 : (A → (OpInvolutiveRingTerm2 n A)) 
      *OL2 : ((OpInvolutiveRingTerm2 n A) → ((OpInvolutiveRingTerm2 n A) → (OpInvolutiveRingTerm2 n A))) 
      +OL2 : ((OpInvolutiveRingTerm2 n A) → ((OpInvolutiveRingTerm2 n A) → (OpInvolutiveRingTerm2 n A))) 
      1OL2 : (OpInvolutiveRingTerm2 n A) 
      primOL2 : ((OpInvolutiveRingTerm2 n A) → (OpInvolutiveRingTerm2 n A)) 
      0OL2 : (OpInvolutiveRingTerm2 n A) 
      negOL2 : ((OpInvolutiveRingTerm2 n A) → (OpInvolutiveRingTerm2 n A))  
      
  simplifyCl :  {A : Set} →  ((ClInvolutiveRingTerm A) → (ClInvolutiveRingTerm A)) 
  simplifyCl (primCl 1Cl) = 1Cl  
  simplifyCl (primCl (primCl x)) = x  
  simplifyCl (+Cl (primCl y) (primCl x)) = (primCl (+Cl x y))  
  simplifyCl (*Cl (primCl y) (primCl x)) = (primCl (*Cl x y))  
  simplifyCl (+Cl 0Cl x) = x  
  simplifyCl (+Cl x 0Cl) = x  
  simplifyCl (*Cl 1Cl x) = x  
  simplifyCl (*Cl x 1Cl) = x  
  simplifyCl (*Cl x1 x2) = (*Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl (+Cl x1 x2) = (+Cl (simplifyCl x1) (simplifyCl x2))  
  simplifyCl 1Cl = 1Cl  
  simplifyCl (primCl x1) = (primCl (simplifyCl x1))  
  simplifyCl 0Cl = 0Cl  
  simplifyCl (negCl x1) = (negCl (simplifyCl x1))  
  simplifyCl (sing x1) = (sing x1)  
  simplifyOpB :  {n : Nat} →  ((OpInvolutiveRingTerm n) → (OpInvolutiveRingTerm n)) 
  simplifyOpB (primOL 1OL) = 1OL  
  simplifyOpB (primOL (primOL x)) = x  
  simplifyOpB (+OL (primOL y) (primOL x)) = (primOL (+OL x y))  
  simplifyOpB (*OL (primOL y) (primOL x)) = (primOL (*OL x y))  
  simplifyOpB (+OL 0OL x) = x  
  simplifyOpB (+OL x 0OL) = x  
  simplifyOpB (*OL 1OL x) = x  
  simplifyOpB (*OL x 1OL) = x  
  simplifyOpB (*OL x1 x2) = (*OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB (+OL x1 x2) = (+OL (simplifyOpB x1) (simplifyOpB x2))  
  simplifyOpB 1OL = 1OL  
  simplifyOpB (primOL x1) = (primOL (simplifyOpB x1))  
  simplifyOpB 0OL = 0OL  
  simplifyOpB (negOL x1) = (negOL (simplifyOpB x1))  
  simplifyOpB (v x1) = (v x1)  
  simplifyOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingTerm2 n A) → (OpInvolutiveRingTerm2 n A)) 
  simplifyOp (primOL2 1OL2) = 1OL2  
  simplifyOp (primOL2 (primOL2 x)) = x  
  simplifyOp (+OL2 (primOL2 y) (primOL2 x)) = (primOL2 (+OL2 x y))  
  simplifyOp (*OL2 (primOL2 y) (primOL2 x)) = (primOL2 (*OL2 x y))  
  simplifyOp (+OL2 0OL2 x) = x  
  simplifyOp (+OL2 x 0OL2) = x  
  simplifyOp (*OL2 1OL2 x) = x  
  simplifyOp (*OL2 x 1OL2) = x  
  simplifyOp (*OL2 x1 x2) = (*OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp (+OL2 x1 x2) = (+OL2 (simplifyOp x1) (simplifyOp x2))  
  simplifyOp 1OL2 = 1OL2  
  simplifyOp (primOL2 x1) = (primOL2 (simplifyOp x1))  
  simplifyOp 0OL2 = 0OL2  
  simplifyOp (negOL2 x1) = (negOL2 (simplifyOp x1))  
  simplifyOp (v2 x1) = (v2 x1)  
  simplifyOp (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveRing A) → (InvolutiveRingTerm → A)) 
  evalB In (*L x1 x2) = ((* In) (evalB In x1) (evalB In x2))  
  evalB In (+L x1 x2) = ((+ In) (evalB In x1) (evalB In x2))  
  evalB In 1L = (1ᵢ In)  
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalB In 0L = (0ᵢ In)  
  evalB In (negL x1) = ((neg In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InvolutiveRing A) → ((ClInvolutiveRingTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (*Cl x1 x2) = ((* In) (evalCl In x1) (evalCl In x2))  
  evalCl In (+Cl x1 x2) = ((+ In) (evalCl In x1) (evalCl In x2))  
  evalCl In 1Cl = (1ᵢ In)  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalCl In 0Cl = (0ᵢ In)  
  evalCl In (negCl x1) = ((neg In) (evalCl In x1))  
  evalOpB :  {A : Set} {n : Nat} →  ((InvolutiveRing A) → ((Vec A n) → ((OpInvolutiveRingTerm n) → A))) 
  evalOpB In vars (v x1) = (lookup vars x1)  
  evalOpB In vars (*OL x1 x2) = ((* In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars (+OL x1 x2) = ((+ In) (evalOpB In vars x1) (evalOpB In vars x2))  
  evalOpB In vars 1OL = (1ᵢ In)  
  evalOpB In vars (primOL x1) = ((prim In) (evalOpB In vars x1))  
  evalOpB In vars 0OL = (0ᵢ In)  
  evalOpB In vars (negOL x1) = ((neg In) (evalOpB In vars x1))  
  evalOp :  {A : Set} {n : Nat} →  ((InvolutiveRing A) → ((Vec A n) → ((OpInvolutiveRingTerm2 n A) → A))) 
  evalOp In vars (v2 x1) = (lookup vars x1)  
  evalOp In vars (sing2 x1) = x1  
  evalOp In vars (*OL2 x1 x2) = ((* In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars (+OL2 x1 x2) = ((+ In) (evalOp In vars x1) (evalOp In vars x2))  
  evalOp In vars 1OL2 = (1ᵢ In)  
  evalOp In vars (primOL2 x1) = ((prim In) (evalOp In vars x1))  
  evalOp In vars 0OL2 = (0ᵢ In)  
  evalOp In vars (negOL2 x1) = ((neg In) (evalOp In vars x1))  
  inductionB :  {P : (InvolutiveRingTerm → Set)} →  (( (x1 x2 : InvolutiveRingTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : InvolutiveRingTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ((P 1L) → (( (x1 : InvolutiveRingTerm) → ((P x1) → (P (primL x1)))) → ((P 0L) → (( (x1 : InvolutiveRingTerm) → ((P x1) → (P (negL x1)))) → ( (x : InvolutiveRingTerm) → (P x)))))))) 
  inductionB p*l p+l p1l ppriml p0l pnegl (*L x1 x2) = (p*l _ _ (inductionB p*l p+l p1l ppriml p0l pnegl x1) (inductionB p*l p+l p1l ppriml p0l pnegl x2))  
  inductionB p*l p+l p1l ppriml p0l pnegl (+L x1 x2) = (p+l _ _ (inductionB p*l p+l p1l ppriml p0l pnegl x1) (inductionB p*l p+l p1l ppriml p0l pnegl x2))  
  inductionB p*l p+l p1l ppriml p0l pnegl 1L = p1l  
  inductionB p*l p+l p1l ppriml p0l pnegl (primL x1) = (ppriml _ (inductionB p*l p+l p1l ppriml p0l pnegl x1))  
  inductionB p*l p+l p1l ppriml p0l pnegl 0L = p0l  
  inductionB p*l p+l p1l ppriml p0l pnegl (negL x1) = (pnegl _ (inductionB p*l p+l p1l ppriml p0l pnegl x1))  
  inductionCl :  {A : Set} {P : ((ClInvolutiveRingTerm A) → Set)} →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClInvolutiveRingTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClInvolutiveRingTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ((P 1Cl) → (( (x1 : (ClInvolutiveRingTerm A)) → ((P x1) → (P (primCl x1)))) → ((P 0Cl) → (( (x1 : (ClInvolutiveRingTerm A)) → ((P x1) → (P (negCl x1)))) → ( (x : (ClInvolutiveRingTerm A)) → (P x))))))))) 
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl (sing x1) = (psing x1)  
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl (*Cl x1 x2) = (p*cl _ _ (inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1) (inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl x2))  
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl (+Cl x1 x2) = (p+cl _ _ (inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1) (inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl x2))  
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl 1Cl = p1cl  
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl (primCl x1) = (pprimcl _ (inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1))  
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl 0Cl = p0cl  
  inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl (negCl x1) = (pnegcl _ (inductionCl psing p*cl p+cl p1cl pprimcl p0cl pnegcl x1))  
  inductionOpB :  {n : Nat} {P : ((OpInvolutiveRingTerm n) → Set)} →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpInvolutiveRingTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ((P 1OL) → (( (x1 : (OpInvolutiveRingTerm n)) → ((P x1) → (P (primOL x1)))) → ((P 0OL) → (( (x1 : (OpInvolutiveRingTerm n)) → ((P x1) → (P (negOL x1)))) → ( (x : (OpInvolutiveRingTerm n)) → (P x))))))))) 
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol (v x1) = (pv x1)  
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol (*OL x1 x2) = (p*ol _ _ (inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol x1) (inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol x2))  
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol (+OL x1 x2) = (p+ol _ _ (inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol x1) (inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol x2))  
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol 1OL = p1ol  
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol (primOL x1) = (pprimol _ (inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol x1))  
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol 0OL = p0ol  
  inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol (negOL x1) = (pnegol _ (inductionOpB pv p*ol p+ol p1ol pprimol p0ol pnegol x1))  
  inductionOp :  {n : Nat} {A : Set} {P : ((OpInvolutiveRingTerm2 n A) → Set)} →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpInvolutiveRingTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpInvolutiveRingTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ((P 1OL2) → (( (x1 : (OpInvolutiveRingTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ((P 0OL2) → (( (x1 : (OpInvolutiveRingTerm2 n A)) → ((P x1) → (P (negOL2 x1)))) → ( (x : (OpInvolutiveRingTerm2 n A)) → (P x)))))))))) 
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (v2 x1) = (pv2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (sing2 x1) = (psing2 x1)  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1) (inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x2))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 1OL2 = p1ol2  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (primOL2 x1) = (pprimol2 _ (inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1))  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 0OL2 = p0ol2  
  inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 (negOL2 x1) = (pnegol2 _ (inductionOp pv2 psing2 p*ol2 p+ol2 p1ol2 pprimol2 p0ol2 pnegol2 x1))  
  stageB :  (InvolutiveRingTerm → (Staged InvolutiveRingTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB 1L = (Now 1L)  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageB 0L = (Now 0L)  
  stageB (negL x1) = (stage1 negL (codeLift1 negL) (stageB x1))  
  stageCl :  {A : Set} →  ((ClInvolutiveRingTerm A) → (Staged (ClInvolutiveRingTerm A))) 
  stageCl (sing x1) = (Now (sing x1))  
  stageCl (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl x1) (stageCl x2))  
  stageCl (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl x1) (stageCl x2))  
  stageCl 1Cl = (Now 1Cl)  
  stageCl (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl x1))  
  stageCl 0Cl = (Now 0Cl)  
  stageCl (negCl x1) = (stage1 negCl (codeLift1 negCl) (stageCl x1))  
  stageOpB :  {n : Nat} →  ((OpInvolutiveRingTerm n) → (Staged (OpInvolutiveRingTerm n))) 
  stageOpB (v x1) = (const (code (v x1)))  
  stageOpB (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB x1) (stageOpB x2))  
  stageOpB (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB x1) (stageOpB x2))  
  stageOpB 1OL = (Now 1OL)  
  stageOpB (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB x1))  
  stageOpB 0OL = (Now 0OL)  
  stageOpB (negOL x1) = (stage1 negOL (codeLift1 negOL) (stageOpB x1))  
  stageOp :  {n : Nat} {A : Set} →  ((OpInvolutiveRingTerm2 n A) → (Staged (OpInvolutiveRingTerm2 n A))) 
  stageOp (sing2 x1) = (Now (sing2 x1))  
  stageOp (v2 x1) = (const (code (v2 x1)))  
  stageOp (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp x1) (stageOp x2))  
  stageOp (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp x1) (stageOp x2))  
  stageOp 1OL2 = (Now 1OL2)  
  stageOp (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp x1))  
  stageOp 0OL2 = (Now 0OL2)  
  stageOp (negOL2 x1) = (stage1 negOL2 (codeLift1 negOL2) (stageOp x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      1T : (Repr A) 
      primT : ((Repr A) → (Repr A)) 
      0T : (Repr A) 
      negT : ((Repr A) → (Repr A))  
  
 