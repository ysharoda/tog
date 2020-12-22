
module AndDeMorgan   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record AndDeMorgan  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      + : (A → (A → A)) 
      prim : (A → A) 
      andDeMorgan_*_+_prim : ( {x y z : A} → (prim (* x y)) ≡ (+ (prim x) (prim y)))  
  
  open AndDeMorgan
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      +S : (AS → (AS → AS)) 
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      primP : ((Prod A A) → (Prod A A)) 
      andDeMorgan_*_+_primP : ( {xP yP zP : (Prod A A)} → (primP (*P xP yP)) ≡ (+P (primP xP) (primP yP)))  
  
  record Hom  {A1 : Set} {A2 : Set} (An1 : (AndDeMorgan A1)) (An2 : (AndDeMorgan A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* An1) x1 x2)) ≡ ((* An2) (hom x1) (hom x2))) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ An1) x1 x2)) ≡ ((+ An2) (hom x1) (hom x2))) 
      pres-prim : ( {x1 : A1} → (hom ((prim An1) x1)) ≡ ((prim An2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (An1 : (AndDeMorgan A1)) (An2 : (AndDeMorgan A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* An1) x1 x2) ((* An2) y1 y2))))) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ An1) x1 x2) ((+ An2) y1 y2))))) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim An1) x1) ((prim An2) y1))))  
  
  data AndDeMorganTerm   : Set where 
      *L : (AndDeMorganTerm → (AndDeMorganTerm → AndDeMorganTerm)) 
      +L : (AndDeMorganTerm → (AndDeMorganTerm → AndDeMorganTerm)) 
      primL : (AndDeMorganTerm → AndDeMorganTerm)  
      
  data ClAndDeMorganTerm  (A : Set) : Set where 
      sing : (A → (ClAndDeMorganTerm A)) 
      *Cl : ((ClAndDeMorganTerm A) → ((ClAndDeMorganTerm A) → (ClAndDeMorganTerm A))) 
      +Cl : ((ClAndDeMorganTerm A) → ((ClAndDeMorganTerm A) → (ClAndDeMorganTerm A))) 
      primCl : ((ClAndDeMorganTerm A) → (ClAndDeMorganTerm A))  
      
  data OpAndDeMorganTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpAndDeMorganTerm n)) 
      *OL : ((OpAndDeMorganTerm n) → ((OpAndDeMorganTerm n) → (OpAndDeMorganTerm n))) 
      +OL : ((OpAndDeMorganTerm n) → ((OpAndDeMorganTerm n) → (OpAndDeMorganTerm n))) 
      primOL : ((OpAndDeMorganTerm n) → (OpAndDeMorganTerm n))  
      
  data OpAndDeMorganTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpAndDeMorganTerm2 n A)) 
      sing2 : (A → (OpAndDeMorganTerm2 n A)) 
      *OL2 : ((OpAndDeMorganTerm2 n A) → ((OpAndDeMorganTerm2 n A) → (OpAndDeMorganTerm2 n A))) 
      +OL2 : ((OpAndDeMorganTerm2 n A) → ((OpAndDeMorganTerm2 n A) → (OpAndDeMorganTerm2 n A))) 
      primOL2 : ((OpAndDeMorganTerm2 n A) → (OpAndDeMorganTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClAndDeMorganTerm A) → (ClAndDeMorganTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpAndDeMorganTerm n) → (OpAndDeMorganTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpAndDeMorganTerm2 n A) → (OpAndDeMorganTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((AndDeMorgan A) → (AndDeMorganTerm → A)) 
  evalB An (*L x1 x2) = ((* An) (evalB An x1) (evalB An x2))  
  evalB An (+L x1 x2) = ((+ An) (evalB An x1) (evalB An x2))  
  evalB An (primL x1) = ((prim An) (evalB An x1))  
  evalCl :  {A : Set} →  ((AndDeMorgan A) → ((ClAndDeMorganTerm A) → A)) 
  evalCl An (sing x1) = x1  
  evalCl An (*Cl x1 x2) = ((* An) (evalCl An x1) (evalCl An x2))  
  evalCl An (+Cl x1 x2) = ((+ An) (evalCl An x1) (evalCl An x2))  
  evalCl An (primCl x1) = ((prim An) (evalCl An x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((AndDeMorgan A) → ((Vec A n) → ((OpAndDeMorganTerm n) → A))) 
  evalOpB n An vars (v x1) = (lookup vars x1)  
  evalOpB n An vars (*OL x1 x2) = ((* An) (evalOpB n An vars x1) (evalOpB n An vars x2))  
  evalOpB n An vars (+OL x1 x2) = ((+ An) (evalOpB n An vars x1) (evalOpB n An vars x2))  
  evalOpB n An vars (primOL x1) = ((prim An) (evalOpB n An vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((AndDeMorgan A) → ((Vec A n) → ((OpAndDeMorganTerm2 n A) → A))) 
  evalOp n An vars (v2 x1) = (lookup vars x1)  
  evalOp n An vars (sing2 x1) = x1  
  evalOp n An vars (*OL2 x1 x2) = ((* An) (evalOp n An vars x1) (evalOp n An vars x2))  
  evalOp n An vars (+OL2 x1 x2) = ((+ An) (evalOp n An vars x1) (evalOp n An vars x2))  
  evalOp n An vars (primOL2 x1) = ((prim An) (evalOp n An vars x1))  
  inductionB :  (P : (AndDeMorganTerm → Set)) →  (( (x1 x2 : AndDeMorganTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 x2 : AndDeMorganTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → (( (x1 : AndDeMorganTerm) → ((P x1) → (P (primL x1)))) → ( (x : AndDeMorganTerm) → (P x))))) 
  inductionB p p*l p+l ppriml (*L x1 x2) = (p*l _ _ (inductionB p p*l p+l ppriml x1) (inductionB p p*l p+l ppriml x2))  
  inductionB p p*l p+l ppriml (+L x1 x2) = (p+l _ _ (inductionB p p*l p+l ppriml x1) (inductionB p p*l p+l ppriml x2))  
  inductionB p p*l p+l ppriml (primL x1) = (ppriml _ (inductionB p p*l p+l ppriml x1))  
  inductionCl :  (A : Set) (P : ((ClAndDeMorganTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClAndDeMorganTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 x2 : (ClAndDeMorganTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → (( (x1 : (ClAndDeMorganTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClAndDeMorganTerm A)) → (P x)))))) 
  inductionCl _ p psing p*cl p+cl pprimcl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl p+cl pprimcl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1) (inductionCl _ p psing p*cl p+cl pprimcl x2))  
  inductionCl _ p psing p*cl p+cl pprimcl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1) (inductionCl _ p psing p*cl p+cl pprimcl x2))  
  inductionCl _ p psing p*cl p+cl pprimcl (primCl x1) = (pprimcl _ (inductionCl _ p psing p*cl p+cl pprimcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpAndDeMorganTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpAndDeMorganTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 x2 : (OpAndDeMorganTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → (( (x1 : (OpAndDeMorganTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpAndDeMorganTerm n)) → (P x)))))) 
  inductionOpB _ p pv p*ol p+ol pprimol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol p+ol pprimol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol p+ol pprimol x1) (inductionOpB _ p pv p*ol p+ol pprimol x2))  
  inductionOpB _ p pv p*ol p+ol pprimol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p*ol p+ol pprimol x1) (inductionOpB _ p pv p*ol p+ol pprimol x2))  
  inductionOpB _ p pv p*ol p+ol pprimol (primOL x1) = (pprimol _ (inductionOpB _ p pv p*ol p+ol pprimol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpAndDeMorganTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpAndDeMorganTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 x2 : (OpAndDeMorganTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → (( (x1 : (OpAndDeMorganTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpAndDeMorganTerm2 n A)) → (P x))))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1))  
  stageB :  (AndDeMorganTerm → (Staged AndDeMorganTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClAndDeMorganTerm A) → (Staged (ClAndDeMorganTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpAndDeMorganTerm n) → (Staged (OpAndDeMorganTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpAndDeMorganTerm2 n A) → (Staged (OpAndDeMorganTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      +T : ((Repr A) → ((Repr A) → (Repr A))) 
      primT : ((Repr A) → (Repr A))  
  
 