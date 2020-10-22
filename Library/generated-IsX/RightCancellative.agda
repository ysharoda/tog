
 module RightCancellative  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRightCancellative (A  : Set ) (op  : (A  → (A  → A ))) (rinv  : (A  → (A  → A )))  : Set where
    constructor IsRightCancellativeC
    field
      rightCancel : ({x y  : A }  → (op (rinv y x ) x ) ≡ y ) 
  
  record RightCancellative (A  : Set )  : Set where
    constructor RightCancellativeC
    field
      op : (A  → (A  → A ))
      rinv : (A  → (A  → A ))
      isRightCancellative : (IsRightCancellative A op rinv ) 
  
  open RightCancellative
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
      rightCancelP : ({xP yP  : (Prod AP AP )}  → (opP (rinvP yP xP ) xP ) ≡ yP ) 
  
  record Hom (A1 A2  : Set ) (Ri1  : (RightCancellative A1 )) (Ri2  : (RightCancellative A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Ri1 ) x1 x2 ) ) ≡ ((rinv Ri2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightCancellative A1 )) (Ri2  : (RightCancellative A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Ri1 ) x1 x2 ) ((rinv Ri2 ) y1 y2 ) )))) 
  
  data RightCancellativeTerm  : Set where
    opL : (RightCancellativeTerm   → (RightCancellativeTerm   → RightCancellativeTerm  ))
    rinvL : (RightCancellativeTerm   → (RightCancellativeTerm   → RightCancellativeTerm  )) 
  
  data ClRightCancellativeTerm (A  : Set )  : Set where
    sing : (A  → (ClRightCancellativeTerm A ) )
    opCl : ((ClRightCancellativeTerm A )  → ((ClRightCancellativeTerm A )  → (ClRightCancellativeTerm A ) ))
    rinvCl : ((ClRightCancellativeTerm A )  → ((ClRightCancellativeTerm A )  → (ClRightCancellativeTerm A ) )) 
  
  data OpRightCancellativeTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightCancellativeTerm n ) )
    opOL : ((OpRightCancellativeTerm n )  → ((OpRightCancellativeTerm n )  → (OpRightCancellativeTerm n ) ))
    rinvOL : ((OpRightCancellativeTerm n )  → ((OpRightCancellativeTerm n )  → (OpRightCancellativeTerm n ) )) 
  
  data OpRightCancellativeTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightCancellativeTerm2 n A ) )
    sing2 : (A  → (OpRightCancellativeTerm2 n A ) )
    opOL2 : ((OpRightCancellativeTerm2 n A )  → ((OpRightCancellativeTerm2 n A )  → (OpRightCancellativeTerm2 n A ) ))
    rinvOL2 : ((OpRightCancellativeTerm2 n A )  → ((OpRightCancellativeTerm2 n A )  → (OpRightCancellativeTerm2 n A ) )) 
  
  simplifyB : (RightCancellativeTerm  → RightCancellativeTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (rinvL x1 x2 )  = (rinvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRightCancellativeTerm A ) → (ClRightCancellativeTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (rinvCl x1 x2 )  = (rinvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRightCancellativeTerm n ) → (OpRightCancellativeTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (rinvOL x1 x2 )  = (rinvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRightCancellativeTerm2 n A ) → (OpRightCancellativeTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (rinvOL2 x1 x2 )  = (rinvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((RightCancellative A ) → (RightCancellativeTerm  → A )))
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (rinvL x1 x2 )  = ((rinv Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightCancellative A ) → ((ClRightCancellativeTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (rinvCl x1 x2 )  = ((rinv Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightCancellative A ) → ((Vec A n ) → ((OpRightCancellativeTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (rinvOL x1 x2 )  = ((rinv Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightCancellative A ) → ((Vec A n ) → ((OpRightCancellativeTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (rinvOL2 x1 x2 )  = ((rinv Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightCancellativeTerm  → Set ))  → (((x1 x2  : RightCancellativeTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : RightCancellativeTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : RightCancellativeTerm )  → (P x )))))
  inductionB p popl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl prinvl x1 ) (inductionB p popl prinvl x2 ) )
  
  inductionB p popl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl prinvl x1 ) (inductionB p popl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightCancellativeTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRightCancellativeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClRightCancellativeTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClRightCancellativeTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl prinvcl x1 ) (inductionCl _ p psing popcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl prinvcl x1 ) (inductionCl _ p psing popcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightCancellativeTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRightCancellativeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpRightCancellativeTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpRightCancellativeTerm n ))  → (P x ))))))
  inductionOp _ p pv popol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol prinvol x1 ) (inductionOp _ p pv popol prinvol x2 ) )
  
  inductionOp _ p pv popol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol prinvol x1 ) (inductionOp _ p pv popol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightCancellativeTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRightCancellativeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpRightCancellativeTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpRightCancellativeTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x2 ) )
  
  opL' : (  (RightCancellativeTerm   → (RightCancellativeTerm   → RightCancellativeTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  rinvL' : (  (RightCancellativeTerm   → (RightCancellativeTerm   → RightCancellativeTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (RightCancellativeTerm  → (Staged RightCancellativeTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClRightCancellativeTerm A )  → ((ClRightCancellativeTerm A )  → (ClRightCancellativeTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClRightCancellativeTerm A )  → ((ClRightCancellativeTerm A )  → (ClRightCancellativeTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightCancellativeTerm A ) → (Staged (ClRightCancellativeTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpRightCancellativeTerm n )  → ((OpRightCancellativeTerm n )  → (OpRightCancellativeTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpRightCancellativeTerm n )  → ((OpRightCancellativeTerm n )  → (OpRightCancellativeTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightCancellativeTerm n ) → (Staged (OpRightCancellativeTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightCancellativeTerm2 n A )  → ((OpRightCancellativeTerm2 n A )  → (OpRightCancellativeTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpRightCancellativeTerm2 n A )  → ((OpRightCancellativeTerm2 n A )  → (OpRightCancellativeTerm2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightCancellativeTerm2 n A ) → (Staged (OpRightCancellativeTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (rinvOL2 x1 x2 )  = (stage2 rinvOL2' (codeLift2 rinvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      rinvT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
