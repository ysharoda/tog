
 module CommutativeAdditiveMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCommutativeAdditiveMagma (A  : Set ) (+  : (A  → (A  → A )))  : Set where
    constructor IsCommutativeAdditiveMagmaC
    field
      commutative_+ : ({x y  : A }  → (+ x y ) ≡ (+ y x )) 
  
  record CommutativeAdditiveMagma (A  : Set )  : Set where
    constructor CommutativeAdditiveMagmaC
    field
      + : (A  → (A  → A ))
      isCommutativeAdditiveMagma : (IsCommutativeAdditiveMagma A (+) ) 
  
  open CommutativeAdditiveMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_+P : ({xP yP  : (Prod AP AP )}  → (+P xP yP ) ≡ (+P yP xP )) 
  
  record Hom (A1 A2  : Set ) (Co1  : (CommutativeAdditiveMagma A1 )) (Co2  : (CommutativeAdditiveMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Co1 ) x1 x2 ) ) ≡ ((+ Co2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Co1  : (CommutativeAdditiveMagma A1 )) (Co2  : (CommutativeAdditiveMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Co1 ) x1 x2 ) ((+ Co2 ) y1 y2 ) )))) 
  
  data CommutativeAdditiveMagmaTerm  : Set where
    +L : (CommutativeAdditiveMagmaTerm   → (CommutativeAdditiveMagmaTerm   → CommutativeAdditiveMagmaTerm  )) 
  
  data ClCommutativeAdditiveMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClCommutativeAdditiveMagmaTerm A ) )
    +Cl : ((ClCommutativeAdditiveMagmaTerm A )  → ((ClCommutativeAdditiveMagmaTerm A )  → (ClCommutativeAdditiveMagmaTerm A ) )) 
  
  data OpCommutativeAdditiveMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCommutativeAdditiveMagmaTerm n ) )
    +OL : ((OpCommutativeAdditiveMagmaTerm n )  → ((OpCommutativeAdditiveMagmaTerm n )  → (OpCommutativeAdditiveMagmaTerm n ) )) 
  
  data OpCommutativeAdditiveMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCommutativeAdditiveMagmaTerm2 n A ) )
    sing2 : (A  → (OpCommutativeAdditiveMagmaTerm2 n A ) )
    +OL2 : ((OpCommutativeAdditiveMagmaTerm2 n A )  → ((OpCommutativeAdditiveMagmaTerm2 n A )  → (OpCommutativeAdditiveMagmaTerm2 n A ) )) 
  
  simplifyB : (CommutativeAdditiveMagmaTerm  → CommutativeAdditiveMagmaTerm )
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClCommutativeAdditiveMagmaTerm A ) → (ClCommutativeAdditiveMagmaTerm A )))
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpCommutativeAdditiveMagmaTerm n ) → (OpCommutativeAdditiveMagmaTerm n )))
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeAdditiveMagmaTerm2 n A ) → (OpCommutativeAdditiveMagmaTerm2 n A )))
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((CommutativeAdditiveMagma A ) → (CommutativeAdditiveMagmaTerm  → A )))
  evalB Co (+L x1 x2 )  = ((+ Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalCl : ({A  : Set }  → ((CommutativeAdditiveMagma A ) → ((ClCommutativeAdditiveMagmaTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co (+Cl x1 x2 )  = ((+ Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CommutativeAdditiveMagma A ) → ((Vec A n ) → ((OpCommutativeAdditiveMagmaTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars (+OL x1 x2 )  = ((+ Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CommutativeAdditiveMagma A ) → ((Vec A n ) → ((OpCommutativeAdditiveMagmaTerm2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars (+OL2 x1 x2 )  = ((+ Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  inductionB : ((P  : (CommutativeAdditiveMagmaTerm  → Set ))  → (((x1 x2  : CommutativeAdditiveMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : CommutativeAdditiveMagmaTerm )  → (P x ))))
  inductionB p p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l x1 ) (inductionB p p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClCommutativeAdditiveMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCommutativeAdditiveMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClCommutativeAdditiveMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl x1 ) (inductionCl _ p psing p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpCommutativeAdditiveMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCommutativeAdditiveMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpCommutativeAdditiveMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol x1 ) (inductionOp _ p pv p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCommutativeAdditiveMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCommutativeAdditiveMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpCommutativeAdditiveMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 x2 ) )
  
  +L' : (  (CommutativeAdditiveMagmaTerm   → (CommutativeAdditiveMagmaTerm   → CommutativeAdditiveMagmaTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (CommutativeAdditiveMagmaTerm  → (Staged CommutativeAdditiveMagmaTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClCommutativeAdditiveMagmaTerm A )  → ((ClCommutativeAdditiveMagmaTerm A )  → (ClCommutativeAdditiveMagmaTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClCommutativeAdditiveMagmaTerm A ) → (Staged (ClCommutativeAdditiveMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpCommutativeAdditiveMagmaTerm n )  → ((OpCommutativeAdditiveMagmaTerm n )  → (OpCommutativeAdditiveMagmaTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpCommutativeAdditiveMagmaTerm n ) → (Staged (OpCommutativeAdditiveMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeAdditiveMagmaTerm2 n A )  → ((OpCommutativeAdditiveMagmaTerm2 n A )  → (OpCommutativeAdditiveMagmaTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeAdditiveMagmaTerm2 n A ) → (Staged (OpCommutativeAdditiveMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
