
 module MiddleCommute  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMiddleCommute (A  : Set ) (op  : (A  → (A  → A )))  : Set where
    constructor IsMiddleCommuteC
    field
      middleCommute_* : ({x y z  : A }  → (op (op (op x y ) z ) x ) ≡ (op (op (op x z ) y ) x )) 
  
  record MiddleCommute (A  : Set )  : Set where
    constructor MiddleCommuteC
    field
      op : (A  → (A  → A ))
      isMiddleCommute : (IsMiddleCommute A op ) 
  
  open MiddleCommute
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      middleCommute_*P : ({xP yP zP  : (Prod AP AP )}  → (opP (opP (opP xP yP ) zP ) xP ) ≡ (opP (opP (opP xP zP ) yP ) xP )) 
  
  record Hom (A1 A2  : Set ) (Mi1  : (MiddleCommute A1 )) (Mi2  : (MiddleCommute A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mi1 ) x1 x2 ) ) ≡ ((op Mi2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mi1  : (MiddleCommute A1 )) (Mi2  : (MiddleCommute A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mi1 ) x1 x2 ) ((op Mi2 ) y1 y2 ) )))) 
  
  data MiddleCommuteTerm  : Set where
    opL : (MiddleCommuteTerm   → (MiddleCommuteTerm   → MiddleCommuteTerm  )) 
  
  data ClMiddleCommuteTerm (A  : Set )  : Set where
    sing : (A  → (ClMiddleCommuteTerm A ) )
    opCl : ((ClMiddleCommuteTerm A )  → ((ClMiddleCommuteTerm A )  → (ClMiddleCommuteTerm A ) )) 
  
  data OpMiddleCommuteTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMiddleCommuteTerm n ) )
    opOL : ((OpMiddleCommuteTerm n )  → ((OpMiddleCommuteTerm n )  → (OpMiddleCommuteTerm n ) )) 
  
  data OpMiddleCommuteTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMiddleCommuteTerm2 n A ) )
    sing2 : (A  → (OpMiddleCommuteTerm2 n A ) )
    opOL2 : ((OpMiddleCommuteTerm2 n A )  → ((OpMiddleCommuteTerm2 n A )  → (OpMiddleCommuteTerm2 n A ) )) 
  
  simplifyB : (MiddleCommuteTerm  → MiddleCommuteTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMiddleCommuteTerm A ) → (ClMiddleCommuteTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMiddleCommuteTerm n ) → (OpMiddleCommuteTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMiddleCommuteTerm2 n A ) → (OpMiddleCommuteTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MiddleCommute A ) → (MiddleCommuteTerm  → A )))
  evalB Mi (opL x1 x2 )  = ((op Mi ) (evalB Mi x1 ) (evalB Mi x2 ) )
  
  evalCl : ({A  : Set }  → ((MiddleCommute A ) → ((ClMiddleCommuteTerm A ) → A )))
  evalCl Mi (sing x1 )  = x1 
  
  evalCl Mi (opCl x1 x2 )  = ((op Mi ) (evalCl Mi x1 ) (evalCl Mi x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MiddleCommute A ) → ((Vec A n ) → ((OpMiddleCommuteTerm n ) → A ))))
  evalOp n Mi vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mi vars (opOL x1 x2 )  = ((op Mi ) (evalOp n Mi vars x1 ) (evalOp n Mi vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MiddleCommute A ) → ((Vec A n ) → ((OpMiddleCommuteTerm2 n A ) → A ))))
  evalOpE n Mi vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mi vars (sing2 x1 )  = x1 
  
  evalOpE n Mi vars (opOL2 x1 x2 )  = ((op Mi ) (evalOpE n Mi vars x1 ) (evalOpE n Mi vars x2 ) )
  
  inductionB : ((P  : (MiddleCommuteTerm  → Set ))  → (((x1 x2  : MiddleCommuteTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : MiddleCommuteTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMiddleCommuteTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMiddleCommuteTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClMiddleCommuteTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMiddleCommuteTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMiddleCommuteTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpMiddleCommuteTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMiddleCommuteTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMiddleCommuteTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpMiddleCommuteTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (MiddleCommuteTerm   → (MiddleCommuteTerm   → MiddleCommuteTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (MiddleCommuteTerm  → (Staged MiddleCommuteTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMiddleCommuteTerm A )  → ((ClMiddleCommuteTerm A )  → (ClMiddleCommuteTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMiddleCommuteTerm A ) → (Staged (ClMiddleCommuteTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMiddleCommuteTerm n )  → ((OpMiddleCommuteTerm n )  → (OpMiddleCommuteTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMiddleCommuteTerm n ) → (Staged (OpMiddleCommuteTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMiddleCommuteTerm2 n A )  → ((OpMiddleCommuteTerm2 n A )  → (OpMiddleCommuteTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMiddleCommuteTerm2 n A ) → (Staged (OpMiddleCommuteTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
