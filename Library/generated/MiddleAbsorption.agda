module MiddleAbsorption  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MiddleAbsorption (A  : Set )  : Set where
    constructor MiddleAbsorptionC
    field
      op : (A  → (A  → A ))
      middleAbsorb_* : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x z ))
  open MiddleAbsorption
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      middleAbsorb_*P : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP zP ))
  record Hom (A1 A2  : Set ) (Mi1  : (MiddleAbsorption A1 )) (Mi2  : (MiddleAbsorption A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mi1 ) x1 x2 ) ) ≡ ((op Mi2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Mi1  : (MiddleAbsorption A1 )) (Mi2  : (MiddleAbsorption A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mi1 ) x1 x2 ) ((op Mi2 ) y1 y2 ) ))))
  data MiddleAbsorptionTerm  : Set where
    opL : (MiddleAbsorptionTerm   → (MiddleAbsorptionTerm   → MiddleAbsorptionTerm  ))
  data ClMiddleAbsorptionTerm (A  : Set )  : Set where
    sing : (A  → (ClMiddleAbsorptionTerm A ) )
    opCl : ((ClMiddleAbsorptionTerm A )  → ((ClMiddleAbsorptionTerm A )  → (ClMiddleAbsorptionTerm A ) ))
  data OpMiddleAbsorptionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMiddleAbsorptionTerm n ) )
    opOL : ((OpMiddleAbsorptionTerm n )  → ((OpMiddleAbsorptionTerm n )  → (OpMiddleAbsorptionTerm n ) ))
  data OpMiddleAbsorptionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMiddleAbsorptionTerm2 n A ) )
    sing2 : (A  → (OpMiddleAbsorptionTerm2 n A ) )
    opOL2 : ((OpMiddleAbsorptionTerm2 n A )  → ((OpMiddleAbsorptionTerm2 n A )  → (OpMiddleAbsorptionTerm2 n A ) ))
  evalB : ({A  : Set }  → ((MiddleAbsorption A ) → (MiddleAbsorptionTerm  → A )))
  evalB Mi (opL x1 x2 )  = ((op Mi ) (evalB Mi x1 ) (evalB Mi x2 ) )
  
  evalCl : ({A  : Set }  → ((MiddleAbsorption A ) → ((ClMiddleAbsorptionTerm A ) → A )))
  evalCl Mi (sing x1 )  = x1 
  
  evalCl Mi (opCl x1 x2 )  = ((op Mi ) (evalCl Mi x1 ) (evalCl Mi x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MiddleAbsorption A ) → ((Vec A n ) → ((OpMiddleAbsorptionTerm n ) → A ))))
  evalOp n Mi vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mi vars (opOL x1 x2 )  = ((op Mi ) (evalOp n Mi vars x1 ) (evalOp n Mi vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MiddleAbsorption A ) → ((Vec A n ) → ((OpMiddleAbsorptionTerm2 n A ) → A ))))
  evalOpE n Mi vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mi vars (sing2 x1 )  = x1 
  
  evalOpE n Mi vars (opOL2 x1 x2 )  = ((op Mi ) (evalOpE n Mi vars x1 ) (evalOpE n Mi vars x2 ) )
  
  inductionB : ((P  : (MiddleAbsorptionTerm  → Set ))  → (((x1 x2  : MiddleAbsorptionTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : MiddleAbsorptionTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMiddleAbsorptionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMiddleAbsorptionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClMiddleAbsorptionTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMiddleAbsorptionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMiddleAbsorptionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpMiddleAbsorptionTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMiddleAbsorptionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMiddleAbsorptionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpMiddleAbsorptionTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (MiddleAbsorptionTerm   → (MiddleAbsorptionTerm   → MiddleAbsorptionTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (MiddleAbsorptionTerm  → (Staged MiddleAbsorptionTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMiddleAbsorptionTerm A )  → ((ClMiddleAbsorptionTerm A )  → (ClMiddleAbsorptionTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMiddleAbsorptionTerm A ) → (Staged (ClMiddleAbsorptionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMiddleAbsorptionTerm n )  → ((OpMiddleAbsorptionTerm n )  → (OpMiddleAbsorptionTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMiddleAbsorptionTerm n ) → (Staged (OpMiddleAbsorptionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMiddleAbsorptionTerm2 n A )  → ((OpMiddleAbsorptionTerm2 n A )  → (OpMiddleAbsorptionTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMiddleAbsorptionTerm2 n A ) → (Staged (OpMiddleAbsorptionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))