module CommutativeMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeMagma (A  : Set )  : Set where
    constructor CommutativeMagmaC
    field
      op : (A  → (A  → A ))
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x ))
  open CommutativeMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP ))
  record Hom (A1 A2  : Set ) (Co1  : (CommutativeMagma A1 )) (Co2  : (CommutativeMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Co1 ) x1 x2 ) ) ≡ ((op Co2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Co1  : (CommutativeMagma A1 )) (Co2  : (CommutativeMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Co1 ) x1 x2 ) ((op Co2 ) y1 y2 ) ))))
  data CommutativeMagmaTerm  : Set where
    opL : (CommutativeMagmaTerm   → (CommutativeMagmaTerm   → CommutativeMagmaTerm  ))
  data ClCommutativeMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClCommutativeMagmaTerm A ) )
    opCl : ((ClCommutativeMagmaTerm A )  → ((ClCommutativeMagmaTerm A )  → (ClCommutativeMagmaTerm A ) ))
  data OpCommutativeMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCommutativeMagmaTerm n ) )
    opOL : ((OpCommutativeMagmaTerm n )  → ((OpCommutativeMagmaTerm n )  → (OpCommutativeMagmaTerm n ) ))
  data OpCommutativeMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCommutativeMagmaTerm2 n A ) )
    sing2 : (A  → (OpCommutativeMagmaTerm2 n A ) )
    opOL2 : ((OpCommutativeMagmaTerm2 n A )  → ((OpCommutativeMagmaTerm2 n A )  → (OpCommutativeMagmaTerm2 n A ) ))
  evalB : ({A  : Set }  → ((CommutativeMagma A ) → (CommutativeMagmaTerm  → A )))
  evalB Co (opL x1 x2 )  = ((op Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalCl : ({A  : Set }  → ((CommutativeMagma A ) → ((ClCommutativeMagmaTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co (opCl x1 x2 )  = ((op Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CommutativeMagma A ) → ((Vec A n ) → ((OpCommutativeMagmaTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars (opOL x1 x2 )  = ((op Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CommutativeMagma A ) → ((Vec A n ) → ((OpCommutativeMagmaTerm2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars (opOL2 x1 x2 )  = ((op Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  inductionB : ((P  : (CommutativeMagmaTerm  → Set ))  → (((x1 x2  : CommutativeMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : CommutativeMagmaTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClCommutativeMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCommutativeMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClCommutativeMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpCommutativeMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCommutativeMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpCommutativeMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCommutativeMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCommutativeMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpCommutativeMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (CommutativeMagmaTerm   → (CommutativeMagmaTerm   → CommutativeMagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (CommutativeMagmaTerm  → (Staged CommutativeMagmaTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClCommutativeMagmaTerm A )  → ((ClCommutativeMagmaTerm A )  → (ClCommutativeMagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClCommutativeMagmaTerm A ) → (Staged (ClCommutativeMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpCommutativeMagmaTerm n )  → ((OpCommutativeMagmaTerm n )  → (OpCommutativeMagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpCommutativeMagmaTerm n ) → (Staged (OpCommutativeMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeMagmaTerm2 n A )  → ((OpCommutativeMagmaTerm2 n A )  → (OpCommutativeMagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeMagmaTerm2 n A ) → (Staged (OpCommutativeMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))