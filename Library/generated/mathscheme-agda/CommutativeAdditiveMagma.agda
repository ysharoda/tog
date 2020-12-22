
module CommutativeAdditiveMagma   where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeAdditiveMagma  (A : Set) : Set where 
     field  
      + : (A → (A → A)) 
      commutative_+ : ( {x y : A} → (+ x y) ≡ (+ y x))  
  
  open CommutativeAdditiveMagma
  record Sig  (AS : Set) : Set where 
     field  
      +S : (AS → (AS → AS))  
  
  record Product  (A : Set) : Set where 
     field  
      +P : ((Prod A A) → ((Prod A A) → (Prod A A))) 
      commutative_+P : ( {xP yP : (Prod A A)} → (+P xP yP) ≡ (+P yP xP))  
  
  record Hom  {A1 : Set} {A2 : Set} (Co1 : (CommutativeAdditiveMagma A1)) (Co2 : (CommutativeAdditiveMagma A2)) : Set where 
     field  
      hom : (A1 → A2) 
      pres-+ : ( {x1 x2 : A1} → (hom ((+ Co1) x1 x2)) ≡ ((+ Co2) (hom x1) (hom x2)))  
  
  record RelInterp  {A1 : Set} {A2 : Set} (Co1 : (CommutativeAdditiveMagma A1)) (Co2 : (CommutativeAdditiveMagma A2)) : Set₁ where 
     field  
      interp : (A1 → (A2 → Set)) 
      interp-+ : ( {x1 x2 : A1} {y1 y2 : A2} → ((interp x1 y1) → ((interp x2 y2) → (interp ((+ Co1) x1 x2) ((+ Co2) y1 y2)))))  
  
  data CommutativeAdditiveMagmaTerm   : Set where 
      +L : (CommutativeAdditiveMagmaTerm → (CommutativeAdditiveMagmaTerm → CommutativeAdditiveMagmaTerm))  
      
  data ClCommutativeAdditiveMagmaTerm  (A : Set) : Set where 
      sing : (A → (ClCommutativeAdditiveMagmaTerm A)) 
      +Cl : ((ClCommutativeAdditiveMagmaTerm A) → ((ClCommutativeAdditiveMagmaTerm A) → (ClCommutativeAdditiveMagmaTerm A)))  
      
  data OpCommutativeAdditiveMagmaTerm  (n : Nat) : Set where 
      v : ((Fin n) → (OpCommutativeAdditiveMagmaTerm n)) 
      +OL : ((OpCommutativeAdditiveMagmaTerm n) → ((OpCommutativeAdditiveMagmaTerm n) → (OpCommutativeAdditiveMagmaTerm n)))  
      
  data OpCommutativeAdditiveMagmaTerm2  (n : Nat) (A : Set) : Set where 
      v2 : ((Fin n) → (OpCommutativeAdditiveMagmaTerm2 n A)) 
      sing2 : (A → (OpCommutativeAdditiveMagmaTerm2 n A)) 
      +OL2 : ((OpCommutativeAdditiveMagmaTerm2 n A) → ((OpCommutativeAdditiveMagmaTerm2 n A) → (OpCommutativeAdditiveMagmaTerm2 n A)))  
      
  simplifyCl :  (A : Set) →  ((ClCommutativeAdditiveMagmaTerm A) → (ClCommutativeAdditiveMagmaTerm A)) 
  simplifyCl _ (+Cl x1 x2) = (+Cl (simplifyCl _ x1) (simplifyCl _ x2))  
  simplifyCl _ (sing x1) = (sing x1)  
  simplifyOpB :  (n : Nat) →  ((OpCommutativeAdditiveMagmaTerm n) → (OpCommutativeAdditiveMagmaTerm n)) 
  simplifyOpB _ (+OL x1 x2) = (+OL (simplifyOpB _ x1) (simplifyOpB _ x2))  
  simplifyOpB _ (v x1) = (v x1)  
  simplifyOp :  (n : Nat) (A : Set) →  ((OpCommutativeAdditiveMagmaTerm2 n A) → (OpCommutativeAdditiveMagmaTerm2 n A)) 
  simplifyOp _ _ (+OL2 x1 x2) = (+OL2 (simplifyOp _ _ x1) (simplifyOp _ _ x2))  
  simplifyOp _ _ (v2 x1) = (v2 x1)  
  simplifyOp _ _ (sing2 x1) = (sing2 x1)  
  evalB :  {A : Set} →  ((CommutativeAdditiveMagma A) → (CommutativeAdditiveMagmaTerm → A)) 
  evalB Co (+L x1 x2) = ((+ Co) (evalB Co x1) (evalB Co x2))  
  evalCl :  {A : Set} →  ((CommutativeAdditiveMagma A) → ((ClCommutativeAdditiveMagmaTerm A) → A)) 
  evalCl Co (sing x1) = x1  
  evalCl Co (+Cl x1 x2) = ((+ Co) (evalCl Co x1) (evalCl Co x2))  
  evalOpB :  {A : Set} (n : Nat) →  ((CommutativeAdditiveMagma A) → ((Vec A n) → ((OpCommutativeAdditiveMagmaTerm n) → A))) 
  evalOpB n Co vars (v x1) = (lookup vars x1)  
  evalOpB n Co vars (+OL x1 x2) = ((+ Co) (evalOpB n Co vars x1) (evalOpB n Co vars x2))  
  evalOp :  {A : Set} (n : Nat) →  ((CommutativeAdditiveMagma A) → ((Vec A n) → ((OpCommutativeAdditiveMagmaTerm2 n A) → A))) 
  evalOp n Co vars (v2 x1) = (lookup vars x1)  
  evalOp n Co vars (sing2 x1) = x1  
  evalOp n Co vars (+OL2 x1 x2) = ((+ Co) (evalOp n Co vars x1) (evalOp n Co vars x2))  
  inductionB :  (P : (CommutativeAdditiveMagmaTerm → Set)) →  (( (x1 x2 : CommutativeAdditiveMagmaTerm) → ((P x1) → ((P x2) → (P (+L x1 x2))))) → ( (x : CommutativeAdditiveMagmaTerm) → (P x))) 
  inductionB p p+l (+L x1 x2) = (p+l _ _ (inductionB p p+l x1) (inductionB p p+l x2))  
  inductionCl :  (A : Set) (P : ((ClCommutativeAdditiveMagmaTerm A) → Set)) →  (( (x1 : A) → (P (sing x1))) → (( (x1 x2 : (ClCommutativeAdditiveMagmaTerm A)) → ((P x1) → ((P x2) → (P (+Cl x1 x2))))) → ( (x : (ClCommutativeAdditiveMagmaTerm A)) → (P x)))) 
  inductionCl _ p psing p+cl (sing x1) = (psing x1)  
  inductionCl _ p psing p+cl (+Cl x1 x2) = (p+cl _ _ (inductionCl _ p psing p+cl x1) (inductionCl _ p psing p+cl x2))  
  inductionOpB :  (n : Nat) (P : ((OpCommutativeAdditiveMagmaTerm n) → Set)) →  (( (fin : (Fin n)) → (P (v fin))) → (( (x1 x2 : (OpCommutativeAdditiveMagmaTerm n)) → ((P x1) → ((P x2) → (P (+OL x1 x2))))) → ( (x : (OpCommutativeAdditiveMagmaTerm n)) → (P x)))) 
  inductionOpB _ p pv p+ol (v x1) = (pv x1)  
  inductionOpB _ p pv p+ol (+OL x1 x2) = (p+ol _ _ (inductionOpB _ p pv p+ol x1) (inductionOpB _ p pv p+ol x2))  
  inductionOp :  (n : Nat) (A : Set) (P : ((OpCommutativeAdditiveMagmaTerm2 n A) → Set)) →  (( (fin : (Fin n)) → (P (v2 fin))) → (( (x1 : A) → (P (sing2 x1))) → (( (x1 x2 : (OpCommutativeAdditiveMagmaTerm2 n A)) → ((P x1) → ((P x2) → (P (+OL2 x1 x2))))) → ( (x : (OpCommutativeAdditiveMagmaTerm2 n A)) → (P x))))) 
  inductionOp _ _ p pv2 psing2 p+ol2 (v2 x1) = (pv2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 (sing2 x1) = (psing2 x1)  
  inductionOp _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2) = (p+ol2 _ _ (inductionOp _ _ p pv2 psing2 p+ol2 x1) (inductionOp _ _ p pv2 psing2 p+ol2 x2))  
  stageB :  (CommutativeAdditiveMagmaTerm → (Staged CommutativeAdditiveMagmaTerm))
  stageB (+L x1 x2) = (stage2 +L (codeLift2 +L) (stageB x1) (stageB x2))  
  stageCl :  (A : Set) →  ((ClCommutativeAdditiveMagmaTerm A) → (Staged (ClCommutativeAdditiveMagmaTerm A))) 
  stageCl _ (sing x1) = (Now (sing x1))  
  stageCl _ (+Cl x1 x2) = (stage2 +Cl (codeLift2 +Cl) (stageCl _ x1) (stageCl _ x2))  
  stageOpB :  (n : Nat) →  ((OpCommutativeAdditiveMagmaTerm n) → (Staged (OpCommutativeAdditiveMagmaTerm n))) 
  stageOpB _ (v x1) = (const (code (v x1)))  
  stageOpB _ (+OL x1 x2) = (stage2 +OL (codeLift2 +OL) (stageOpB _ x1) (stageOpB _ x2))  
  stageOp :  (n : Nat) (A : Set) →  ((OpCommutativeAdditiveMagmaTerm2 n A) → (Staged (OpCommutativeAdditiveMagmaTerm2 n A))) 
  stageOp _ _ (sing2 x1) = (Now (sing2 x1))  
  stageOp _ _ (v2 x1) = (const (code (v2 x1)))  
  stageOp _ _ (+OL2 x1 x2) = (stage2 +OL2 (codeLift2 +OL2) (stageOp _ _ x1) (stageOp _ _ x2))  
  record StagedRepr  (A : Set) (Repr : (Set → Set)) : Set where 
     field  
      +T : ((Repr A) → ((Repr A) → (Repr A)))  
  
 