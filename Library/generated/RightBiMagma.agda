module RightBiMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightBiMagma (A  : Set )  : Set where
    constructor RightBiMagmaC
    field
      op : (A  → (A  → A ))
      rinv : (A  → (A  → A ))
  open RightBiMagma
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
  record Hom (A1 A2  : Set ) (Ri1  : (RightBiMagma A1 )) (Ri2  : (RightBiMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Ri1 ) x1 x2 ) ) ≡ ((rinv Ri2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightBiMagma A1 )) (Ri2  : (RightBiMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Ri1 ) x1 x2 ) ((rinv Ri2 ) y1 y2 ) ))))
  data RightBiMagmaTerm  : Set where
    opL : (RightBiMagmaTerm   → (RightBiMagmaTerm   → RightBiMagmaTerm  ))
    rinvL : (RightBiMagmaTerm   → (RightBiMagmaTerm   → RightBiMagmaTerm  ))
  data ClRightBiMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClRightBiMagmaTerm A ) )
    opCl : ((ClRightBiMagmaTerm A )  → ((ClRightBiMagmaTerm A )  → (ClRightBiMagmaTerm A ) ))
    rinvCl : ((ClRightBiMagmaTerm A )  → ((ClRightBiMagmaTerm A )  → (ClRightBiMagmaTerm A ) ))
  data OpRightBiMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightBiMagmaTerm n ) )
    opOL : ((OpRightBiMagmaTerm n )  → ((OpRightBiMagmaTerm n )  → (OpRightBiMagmaTerm n ) ))
    rinvOL : ((OpRightBiMagmaTerm n )  → ((OpRightBiMagmaTerm n )  → (OpRightBiMagmaTerm n ) ))
  data OpRightBiMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightBiMagmaTerm2 n A ) )
    sing2 : (A  → (OpRightBiMagmaTerm2 n A ) )
    opOL2 : ((OpRightBiMagmaTerm2 n A )  → ((OpRightBiMagmaTerm2 n A )  → (OpRightBiMagmaTerm2 n A ) ))
    rinvOL2 : ((OpRightBiMagmaTerm2 n A )  → ((OpRightBiMagmaTerm2 n A )  → (OpRightBiMagmaTerm2 n A ) ))
  evalB : ({A  : Set }  → ((RightBiMagma A ) → (RightBiMagmaTerm  → A )))
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (rinvL x1 x2 )  = ((rinv Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightBiMagma A ) → ((ClRightBiMagmaTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (rinvCl x1 x2 )  = ((rinv Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightBiMagma A ) → ((Vec A n ) → ((OpRightBiMagmaTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (rinvOL x1 x2 )  = ((rinv Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightBiMagma A ) → ((Vec A n ) → ((OpRightBiMagmaTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (rinvOL2 x1 x2 )  = ((rinv Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightBiMagmaTerm  → Set ))  → (((x1 x2  : RightBiMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : RightBiMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : RightBiMagmaTerm )  → (P x )))))
  inductionB p popl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl prinvl x1 ) (inductionB p popl prinvl x2 ) )
  
  inductionB p popl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl prinvl x1 ) (inductionB p popl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightBiMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRightBiMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClRightBiMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClRightBiMagmaTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl prinvcl x1 ) (inductionCl _ p psing popcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl prinvcl x1 ) (inductionCl _ p psing popcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightBiMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRightBiMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpRightBiMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpRightBiMagmaTerm n ))  → (P x ))))))
  inductionOp _ p pv popol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol prinvol x1 ) (inductionOp _ p pv popol prinvol x2 ) )
  
  inductionOp _ p pv popol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol prinvol x1 ) (inductionOp _ p pv popol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightBiMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRightBiMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpRightBiMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpRightBiMagmaTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 prinvol2 x2 ) )
  
  opL' : (  (RightBiMagmaTerm   → (RightBiMagmaTerm   → RightBiMagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  rinvL' : (  (RightBiMagmaTerm   → (RightBiMagmaTerm   → RightBiMagmaTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (RightBiMagmaTerm  → (Staged RightBiMagmaTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClRightBiMagmaTerm A )  → ((ClRightBiMagmaTerm A )  → (ClRightBiMagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClRightBiMagmaTerm A )  → ((ClRightBiMagmaTerm A )  → (ClRightBiMagmaTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightBiMagmaTerm A ) → (Staged (ClRightBiMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpRightBiMagmaTerm n )  → ((OpRightBiMagmaTerm n )  → (OpRightBiMagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpRightBiMagmaTerm n )  → ((OpRightBiMagmaTerm n )  → (OpRightBiMagmaTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightBiMagmaTerm n ) → (Staged (OpRightBiMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightBiMagmaTerm2 n A )  → ((OpRightBiMagmaTerm2 n A )  → (OpRightBiMagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpRightBiMagmaTerm2 n A )  → ((OpRightBiMagmaTerm2 n A )  → (OpRightBiMagmaTerm2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightBiMagmaTerm2 n A ) → (Staged (OpRightBiMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (rinvOL2 x1 x2 )  = (stage2 rinvOL2' (codeLift2 rinvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      rinvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))