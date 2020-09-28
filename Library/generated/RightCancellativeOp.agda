module RightCancellativeOp  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightCancellativeOp (A  : Set )  : Set where
    constructor RightCancellativeOpC
    field
      op : (A  → (A  → A ))
      rinv : (A  → (A  → A ))
      rightCancelOp : ({x y  : A }  → (rinv (op y x ) x ) ≡ y )
  open RightCancellativeOp
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      rinvS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      rinvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      rightCancelOpP : ({xP yP  : (Prod AP AP )}  → (rinvP (opP yP xP ) xP ) ≡ yP )
  record Hom (A1 A2  : Set ) (Ri1  : (RightCancellativeOp A1 )) (Ri2  : (RightCancellativeOp A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Ri1 ) x1 x2 ) ) ≡ ((rinv Ri2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightCancellativeOp A1 )) (Ri2  : (RightCancellativeOp A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Ri1 ) x1 x2 ) ((rinv Ri2 ) y1 y2 ) ))))
  data RightCancellativeOpTerm  : Set where
    opL : (RightCancellativeOpTerm   → (RightCancellativeOpTerm   → RightCancellativeOpTerm  ))
    rinvL : (RightCancellativeOpTerm   → (RightCancellativeOpTerm   → RightCancellativeOpTerm  ))
  data ClRightCancellativeOpTerm (A  : Set )  : Set where
    sing : (A  → (ClRightCancellativeOpTerm A ) )
    opCl : ((ClRightCancellativeOpTerm A )  → ((ClRightCancellativeOpTerm A )  → (ClRightCancellativeOpTerm A ) ))
    rinvCl : ((ClRightCancellativeOpTerm A )  → ((ClRightCancellativeOpTerm A )  → (ClRightCancellativeOpTerm A ) ))
  data OpRightCancellativeOpTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightCancellativeOpTerm n ) )
    opOL : ((OpRightCancellativeOpTerm n )  → ((OpRightCancellativeOpTerm n )  → (OpRightCancellativeOpTerm n ) ))
    rinvOL : ((OpRightCancellativeOpTerm n )  → ((OpRightCancellativeOpTerm n )  → (OpRightCancellativeOpTerm n ) ))
  data OpRightCancellativeOpTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightCancellativeOpTerm2 n A ) )
    sing2 : (A  → (OpRightCancellativeOpTerm2 n A ) )
    opOL2 : ((OpRightCancellativeOpTerm2 n A )  → ((OpRightCancellativeOpTerm2 n A )  → (OpRightCancellativeOpTerm2 n A ) ))
    rinvOL2 : ((OpRightCancellativeOpTerm2 n A )  → ((OpRightCancellativeOpTerm2 n A )  → (OpRightCancellativeOpTerm2 n A ) ))
  evalB : ({A  : Set }  → ((RightCancellativeOp A ) → (RightCancellativeOpTerm  → A )))
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (rinvL x1 x2 )  = ((rinv Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightCancellativeOp A ) → ((ClRightCancellativeOpTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (rinvCl x1 x2 )  = ((rinv Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightCancellativeOp A ) → ((Vec A n ) → ((OpRightCancellativeOpTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (rinvOL x1 x2 )  = ((rinv Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightCancellativeOp A ) → ((Vec A n ) → ((OpRightCancellativeOpTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (rinvOL2 x1 x2 )  = ((rinv Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightCancellativeOpTerm  → Set ))  → (((x1 x2  : RightCancellativeOpTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : RightCancellativeOpTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : RightCancellativeOpTerm )  → (P x )))))
  inductionB p popl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl prinvl x1 ) (inductionB p popl prinvl x2 ) )
  
  inductionB p popl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl prinvl x1 ) (inductionB p popl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightCancellativeOpTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRightCancellativeOpTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClRightCancellativeOpTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClRightCancellativeOpTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl prinvcl x1 ) (inductionCl _ p psing popcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl prinvcl x1 ) (inductionCl _ p psing popcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightCancellativeOpTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRightCancellativeOpTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpRightCancellativeOpTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpRightCancellativeOpTerm n ))  → (P x ))))))
  inductionOp _ p pv popol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol prinvol x1 ) (inductionOp _ p pv popol prinvol x2 ) )
  
  inductionOp _ p pv popol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol prinvol x1 ) (inductionOp _ p pv popol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightCancellativeOpTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRightCancellativeOpTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpRightCancellativeOpTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpRightCancellativeOpTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x2 ) )
  
  opL' : (  (RightCancellativeOpTerm   → (RightCancellativeOpTerm   → RightCancellativeOpTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  rinvL' : (  (RightCancellativeOpTerm   → (RightCancellativeOpTerm   → RightCancellativeOpTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (RightCancellativeOpTerm  → (Staged RightCancellativeOpTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClRightCancellativeOpTerm A )  → ((ClRightCancellativeOpTerm A )  → (ClRightCancellativeOpTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClRightCancellativeOpTerm A )  → ((ClRightCancellativeOpTerm A )  → (ClRightCancellativeOpTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightCancellativeOpTerm A ) → (Staged (ClRightCancellativeOpTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpRightCancellativeOpTerm n )  → ((OpRightCancellativeOpTerm n )  → (OpRightCancellativeOpTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpRightCancellativeOpTerm n )  → ((OpRightCancellativeOpTerm n )  → (OpRightCancellativeOpTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightCancellativeOpTerm n ) → (Staged (OpRightCancellativeOpTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightCancellativeOpTerm2 n A )  → ((OpRightCancellativeOpTerm2 n A )  → (OpRightCancellativeOpTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpRightCancellativeOpTerm2 n A )  → ((OpRightCancellativeOpTerm2 n A )  → (OpRightCancellativeOpTerm2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightCancellativeOpTerm2 n A ) → (Staged (OpRightCancellativeOpTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (rinvOL2 x1 x2 )  = (stage2 rinvOL2' (codeLift2 rinvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      rinvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))