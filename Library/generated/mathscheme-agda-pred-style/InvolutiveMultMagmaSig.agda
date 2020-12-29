
module InvolutiveMultMagmaSig   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveMultMagmaSig  (A : Set) (* : (A → (A → A))) (prim : (A → A)) : Set where 
    
  record InvolutiveMultMagmaSig  (A : Set) : Set where 
     field  
      * : (A → (A → A)) 
      prim : (A → A) 
      isInvolutiveMultMagmaSig : (IsInvolutiveMultMagmaSig A (*) prim)  
  
  open InvolutiveMultMagmaSig
  record Sig  (AS : Set) : Set where 
     field  
      *S : (AS → (AS → AS)) 
      primS : (AS → AS)  
  
  record Product  (A : Set) : Set where 
     field  
      *P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      primP : ((Prod A A) → (Prod A A))  
  
  record Hom  {A1 : Set} {A2 : Set} (In1 : (InvolutiveMultMagmaSig A1)) (In2 : (InvolutiveMultMagmaSig A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-* : ( {x1 x2 : A1} → (hom ((* In1) x1 x2)) ≡ ((* In2) (hom x1) (hom x2))) 
      pres-prim : ( {x1 : A1} → (hom ((prim In1) x1)) ≡ ((prim In2) (hom x1)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (In1 : (InvolutiveMultMagmaSig A1)) (In2 : (InvolutiveMultMagmaSig A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-* : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((* In1) x1 x2) ((* In2) y1 y2))))) 
      interp-prim : ( {x1 : A1} {y1 : A2} → ((interp x1 y1) → (interp ((prim In1) x1) ((prim In2) y1))))  
  
  data InvolutiveMultMagmaSigTerm   : Set where 
      *L : (InvolutiveMultMagmaSigTerm → (InvolutiveMultMagmaSigTerm → InvolutiveMultMagmaSigTerm)) 
      primL : (InvolutiveMultMagmaSigTerm → InvolutiveMultMagmaSigTerm)  
      
  data ClInvolutiveMultMagmaSigTerm  (A : Set) : Set where 
      sing : (A → (ClInvolutiveMultMagmaSigTerm A)) 
      *Cl : ((ClInvolutiveMultMagmaSigTerm A) → ((ClInvolutiveMultMagmaSigTerm A) → (ClInvolutiveMultMagmaSigTerm A))) 
      primCl : ((ClInvolutiveMultMagmaSigTerm A) → (ClInvolutiveMultMagmaSigTerm A))  
      
  data OpInvolutiveMultMagmaSigTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpInvolutiveMultMagmaSigTerm n)) 
      *OL : ((OpInvolutiveMultMagmaSigTerm n) → ((OpInvolutiveMultMagmaSigTerm n) → (OpInvolutiveMultMagmaSigTerm n))) 
      primOL : ((OpInvolutiveMultMagmaSigTerm n) → (OpInvolutiveMultMagmaSigTerm n))  
      
  data OpInvolutiveMultMagmaSigTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpInvolutiveMultMagmaSigTerm2 n A)) 
      sing2 : (A → (OpInvolutiveMultMagmaSigTerm2 n A)) 
      *OL2 : ((OpInvolutiveMultMagmaSigTerm2 n A) → ((OpInvolutiveMultMagmaSigTerm2 n A) → (OpInvolutiveMultMagmaSigTerm2 n A))) 
      primOL2 : ((OpInvolutiveMultMagmaSigTerm2 n A) → (OpInvolutiveMultMagmaSigTerm2 n A))  
      
  simplifyCl :  (A : Set) →  ((ClInvolutiveMultMagmaSigTerm A) → (ClInvolutiveMultMagmaSigTerm A)) 
  simplifyCl _ (*Cl x1 x2) = (*Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (primCl x1) = (primCl (simplifyCl _ x1))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpInvolutiveMultMagmaSigTerm n) → (OpInvolutiveMultMagmaSigTerm n)) 
  simplifyOpB _ (*OL x1 x2) = (*OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (primOL x1) = (primOL (simplifyOpB _ x1))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpInvolutiveMultMagmaSigTerm2 n A) → (OpInvolutiveMultMagmaSigTerm2 n A)) 
  simplifyOp _ _ (*OL2 x1 x2) = (*OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (primOL2 x1) = (primOL2 (simplifyOp _ _ x1))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((InvolutiveMultMagmaSig A) → (InvolutiveMultMagmaSigTerm → A)) 
  evalB In (*L x1 x2) = ((* In) (evalB In x1) (evalB In x2))  
  evalB In (primL x1) = ((prim In) (evalB In x1))  
  evalCl :  {A : Set} →  ((InvolutiveMultMagmaSig A) → ((ClInvolutiveMultMagmaSigTerm A) → A)) 
  evalCl In (sing x1) = x1  
  evalCl In (*Cl x1 x2) = ((* In) (evalCl In x1) (evalCl In x2))  
  evalCl In (primCl x1) = ((prim In) (evalCl In x1))  
  evalOpB :  {A : Set} (n : Nat) →  ((InvolutiveMultMagmaSig A) → ((Vec A n) → ((OpInvolutiveMultMagmaSigTerm n) → A))) 
  evalOpB n In vars (v x1) = (lookup vars x1)  
  evalOpB n In vars (*OL x1 x2) = ((* In) (evalOpB n In vars x1) (evalOpB n In vars x2))  
  evalOpB n In vars (primOL x1) = ((prim In) (evalOpB n In vars x1))  
  evalOp :  {A : Set} (n : Nat) →  ((InvolutiveMultMagmaSig A) → ((Vec A n) → ((OpInvolutiveMultMagmaSigTerm2 n A) → A))) 
  evalOp n In vars (v2 x1) = (lookup vars x1)  
  evalOp n In vars (sing2 x1) = x1  
  evalOp n In vars (*OL2 x1 x2) = ((* In) (evalOp n In vars x1) (evalOp n In vars x2))  
  evalOp n In vars (primOL2 x1) = ((prim In) (evalOp n In vars x1))  
  inductionB :  (P : (InvolutiveMultMagmaSigTerm → Set)) →  (( (x1 x2 : InvolutiveMultMagmaSigTerm) → ((P x1) → ((P x2) → (P (*L x1 x2))))) → (( (x1 : InvolutiveMultMagmaSigTerm) → ((P x1) → (P (primL x1)))) → ( (x : InvolutiveMultMagmaSigTerm) → (P x)))) 
  inductionB p p*l ppriml (*L x1 x2) = (p*l _ _ (inductionB p p*l ppriml x1) (inductionB p p*l ppriml x2))  
  inductionB p p*l ppriml (primL x1) = (ppriml _ (inductionB p p*l ppriml x1))  
  inductionCl :  (A : Set) (P : ((ClInvolutiveMultMagmaSigTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClInvolutiveMultMagmaSigTerm A)) → ((P x1) → ((P x2) → (P (*Cl x1 x2))))) → (( (x1 : (ClInvolutiveMultMagmaSigTerm A)) → ((P x1) → (P (primCl x1)))) → ( (x : (ClInvolutiveMultMagmaSigTerm A)) → (P x))))) 
  inductionCl _ p psing p*cl pprimcl (sing x1) = (psing x1)  
  inductionCl _ p psing p*cl pprimcl (*Cl x1 x2) = (p*cl _ _ (inductionCl _ p psing p*cl pprimcl x1) (inductionCl _ p psing p*cl pprimcl x2))  
  inductionCl _ p psing p*cl pprimcl (primCl x1) = (pprimcl _ (inductionCl _ p psing p*cl pprimcl x1))  
  inductionOpB :  (n : Nat) (P : ((OpInvolutiveMultMagmaSigTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpInvolutiveMultMagmaSigTerm n)) → ((P x1) → ((P x2) → (P (*OL x1 x2))))) → (( (x1 : (OpInvolutiveMultMagmaSigTerm n)) → ((P x1) → (P (primOL x1)))) → ( (x : (OpInvolutiveMultMagmaSigTerm n)) → (P x))))) 
  inductionOpB _ p pv p*ol pprimol (v x1) = (pv x1)  
  inductionOpB _ p pv p*ol pprimol (*OL x1 x2) = (p*ol _ _ (inductionOpB _ p pv p*ol pprimol x1) (inductionOpB _ p pv p*ol pprimol x2))  
  inductionOpB _ p pv p*ol pprimol (primOL x1) = (pprimol _ (inductionOpB _ p pv p*ol pprimol x1))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpInvolutiveMultMagmaSigTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpInvolutiveMultMagmaSigTerm2 n A)) → ((P x1) → ((P x2) → (P (*OL2 x1 x2))))) → (( (x1 : (OpInvolutiveMultMagmaSigTerm2 n A)) → ((P x1) → (P (primOL2 x1)))) → ( (x : (OpInvolutiveMultMagmaSigTerm2 n A)) → (P x)))))) 
  inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 (*OL2 x1 x2) = (p*ol2 _ _ (inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 x1) (inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 x2))  
  inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 (primOL2 x1) = (pprimol2 _ (inductionOp _ _ p pv2 psing2 p*ol2 pprimol2 x1))  
  stageB :  (InvolutiveMultMagmaSigTerm → (Staged InvolutiveMultMagmaSigTerm))
  stageB (*L x1 x2) = (stage2 *L (codeLift2 *L) (stageB x1) (stageB x2))  
  stageB (primL x1) = (stage1 primL (codeLift1 primL) (stageB x1))  
  stageCl :  (A : Set) →  ((ClInvolutiveMultMagmaSigTerm A) → (Staged (ClInvolutiveMultMagmaSigTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (*Cl x1 x2) = (stage2 *Cl (codeLift2 *Cl) (stageCl _ x1) (stageCl _ x2))  
  stageCl _ (primCl x1) = (stage1 primCl (codeLift1 primCl) (stageCl _ x1))  
  stageOpB :  (n : Nat) →  ((OpInvolutiveMultMagmaSigTerm n) → (Staged (OpInvolutiveMultMagmaSigTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (*OL x1 x2) = (stage2 *OL (codeLift2 *OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOpB _ (primOL x1) = (stage1 primOL (codeLift1 primOL) (stageOpB _ x1))  
  stageOp :  (n : Nat) (A : Set) →  ((OpInvolutiveMultMagmaSigTerm2 n A) → (Staged (OpInvolutiveMultMagmaSigTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (*OL2 x1 x2) = (stage2 *OL2 (codeLift2 *OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  stageOp _ _ (primOL2 x1) = (stage1 primOL2 (codeLift1 primOL2) (stageOp _ _ x1))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      *T : ((Repr A) → ((Repr A) → (Repr A))) 
      primT : ((Repr A) → (Repr A))  
  
 