module QuasiGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record QuasiGroup (A  : Set )  : Set where
    constructor QuasiGroupC
    field
      op : (A  → (A  → A ))
      linv : (A  → (A  → A ))
      leftCancel : ({x y  : A }  → (op x (linv x y ) ) ≡ y )
      lefCancelOp : ({x y  : A }  → (linv x (op x y ) ) ≡ y )
      rinv : (A  → (A  → A ))
      rightCancel : ({x y  : A }  → (op (rinv y x ) x ) ≡ y )
      rightCancelOp : ({x y  : A }  → (rinv (op y x ) x ) ≡ y )
  open QuasiGroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      linvS : (AS  → (AS  → AS ))
      rinvS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      linvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      rinvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftCancelP : ({xP yP  : (Prod AP AP )}  → (opP xP (linvP xP yP ) ) ≡ yP )
      lefCancelOpP : ({xP yP  : (Prod AP AP )}  → (linvP xP (opP xP yP ) ) ≡ yP )
      rightCancelP : ({xP yP  : (Prod AP AP )}  → (opP (rinvP yP xP ) xP ) ≡ yP )
      rightCancelOpP : ({xP yP  : (Prod AP AP )}  → (rinvP (opP yP xP ) xP ) ≡ yP )
  record Hom (A1 A2  : Set ) (Qu1  : (QuasiGroup A1 )) (Qu2  : (QuasiGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Qu1 ) x1 x2 ) ) ≡ ((op Qu2 ) (hom x1 ) (hom x2 ) ))
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Qu1 ) x1 x2 ) ) ≡ ((linv Qu2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Qu1 ) x1 x2 ) ) ≡ ((rinv Qu2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Qu1  : (QuasiGroup A1 )) (Qu2  : (QuasiGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Qu1 ) x1 x2 ) ((op Qu2 ) y1 y2 ) ))))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Qu1 ) x1 x2 ) ((linv Qu2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Qu1 ) x1 x2 ) ((rinv Qu2 ) y1 y2 ) ))))
  data QuasiGroupTerm  : Set where
    opL : (QuasiGroupTerm   → (QuasiGroupTerm   → QuasiGroupTerm  ))
    linvL : (QuasiGroupTerm   → (QuasiGroupTerm   → QuasiGroupTerm  ))
    rinvL : (QuasiGroupTerm   → (QuasiGroupTerm   → QuasiGroupTerm  ))
  data ClQuasiGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClQuasiGroupTerm A ) )
    opCl : ((ClQuasiGroupTerm A )  → ((ClQuasiGroupTerm A )  → (ClQuasiGroupTerm A ) ))
    linvCl : ((ClQuasiGroupTerm A )  → ((ClQuasiGroupTerm A )  → (ClQuasiGroupTerm A ) ))
    rinvCl : ((ClQuasiGroupTerm A )  → ((ClQuasiGroupTerm A )  → (ClQuasiGroupTerm A ) ))
  data OpQuasiGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpQuasiGroupTerm n ) )
    opOL : ((OpQuasiGroupTerm n )  → ((OpQuasiGroupTerm n )  → (OpQuasiGroupTerm n ) ))
    linvOL : ((OpQuasiGroupTerm n )  → ((OpQuasiGroupTerm n )  → (OpQuasiGroupTerm n ) ))
    rinvOL : ((OpQuasiGroupTerm n )  → ((OpQuasiGroupTerm n )  → (OpQuasiGroupTerm n ) ))
  data OpQuasiGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpQuasiGroupTerm2 n A ) )
    sing2 : (A  → (OpQuasiGroupTerm2 n A ) )
    opOL2 : ((OpQuasiGroupTerm2 n A )  → ((OpQuasiGroupTerm2 n A )  → (OpQuasiGroupTerm2 n A ) ))
    linvOL2 : ((OpQuasiGroupTerm2 n A )  → ((OpQuasiGroupTerm2 n A )  → (OpQuasiGroupTerm2 n A ) ))
    rinvOL2 : ((OpQuasiGroupTerm2 n A )  → ((OpQuasiGroupTerm2 n A )  → (OpQuasiGroupTerm2 n A ) ))
  evalB : ({A  : Set }  → ((QuasiGroup A ) → (QuasiGroupTerm  → A )))
  evalB Qu (opL x1 x2 )  = ((op Qu ) (evalB Qu x1 ) (evalB Qu x2 ) )
  
  evalB Qu (linvL x1 x2 )  = ((linv Qu ) (evalB Qu x1 ) (evalB Qu x2 ) )
  
  evalB Qu (rinvL x1 x2 )  = ((rinv Qu ) (evalB Qu x1 ) (evalB Qu x2 ) )
  
  evalCl : ({A  : Set }  → ((QuasiGroup A ) → ((ClQuasiGroupTerm A ) → A )))
  evalCl Qu (sing x1 )  = x1 
  
  evalCl Qu (opCl x1 x2 )  = ((op Qu ) (evalCl Qu x1 ) (evalCl Qu x2 ) )
  
  evalCl Qu (linvCl x1 x2 )  = ((linv Qu ) (evalCl Qu x1 ) (evalCl Qu x2 ) )
  
  evalCl Qu (rinvCl x1 x2 )  = ((rinv Qu ) (evalCl Qu x1 ) (evalCl Qu x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((QuasiGroup A ) → ((Vec A n ) → ((OpQuasiGroupTerm n ) → A ))))
  evalOp n Qu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Qu vars (opOL x1 x2 )  = ((op Qu ) (evalOp n Qu vars x1 ) (evalOp n Qu vars x2 ) )
  
  evalOp n Qu vars (linvOL x1 x2 )  = ((linv Qu ) (evalOp n Qu vars x1 ) (evalOp n Qu vars x2 ) )
  
  evalOp n Qu vars (rinvOL x1 x2 )  = ((rinv Qu ) (evalOp n Qu vars x1 ) (evalOp n Qu vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((QuasiGroup A ) → ((Vec A n ) → ((OpQuasiGroupTerm2 n A ) → A ))))
  evalOpE n Qu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Qu vars (sing2 x1 )  = x1 
  
  evalOpE n Qu vars (opOL2 x1 x2 )  = ((op Qu ) (evalOpE n Qu vars x1 ) (evalOpE n Qu vars x2 ) )
  
  evalOpE n Qu vars (linvOL2 x1 x2 )  = ((linv Qu ) (evalOpE n Qu vars x1 ) (evalOpE n Qu vars x2 ) )
  
  evalOpE n Qu vars (rinvOL2 x1 x2 )  = ((rinv Qu ) (evalOpE n Qu vars x1 ) (evalOpE n Qu vars x2 ) )
  
  inductionB : ((P  : (QuasiGroupTerm  → Set ))  → (((x1 x2  : QuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : QuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → (((x1 x2  : QuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : QuasiGroupTerm )  → (P x ))))))
  inductionB p popl plinvl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionB p popl plinvl prinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionB p popl plinvl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClQuasiGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → (((x1 x2  : (ClQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClQuasiGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl plinvcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl plinvcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl prinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpQuasiGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → (((x1 x2  : (OpQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpQuasiGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv popol plinvol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol plinvol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol plinvol prinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol plinvol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpQuasiGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → (((x1 x2  : (OpQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpQuasiGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  opL' : (  (QuasiGroupTerm   → (QuasiGroupTerm   → QuasiGroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  linvL' : (  (QuasiGroupTerm   → (QuasiGroupTerm   → QuasiGroupTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  rinvL' : (  (QuasiGroupTerm   → (QuasiGroupTerm   → QuasiGroupTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (QuasiGroupTerm  → (Staged QuasiGroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClQuasiGroupTerm A )  → ((ClQuasiGroupTerm A )  → (ClQuasiGroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  linvCl' : ({A  : Set }  → ((ClQuasiGroupTerm A )  → ((ClQuasiGroupTerm A )  → (ClQuasiGroupTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClQuasiGroupTerm A )  → ((ClQuasiGroupTerm A )  → (ClQuasiGroupTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClQuasiGroupTerm A ) → (Staged (ClQuasiGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpQuasiGroupTerm n )  → ((OpQuasiGroupTerm n )  → (OpQuasiGroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  linvOL' : ({n  : Nat}  → ((OpQuasiGroupTerm n )  → ((OpQuasiGroupTerm n )  → (OpQuasiGroupTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpQuasiGroupTerm n )  → ((OpQuasiGroupTerm n )  → (OpQuasiGroupTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpQuasiGroupTerm n ) → (Staged (OpQuasiGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpQuasiGroupTerm2 n A )  → ((OpQuasiGroupTerm2 n A )  → (OpQuasiGroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpQuasiGroupTerm2 n A )  → ((OpQuasiGroupTerm2 n A )  → (OpQuasiGroupTerm2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpQuasiGroupTerm2 n A )  → ((OpQuasiGroupTerm2 n A )  → (OpQuasiGroupTerm2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpQuasiGroupTerm2 n A ) → (Staged (OpQuasiGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (linvOL2 x1 x2 )  = (stage2 linvOL2' (codeLift2 linvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (rinvOL2 x1 x2 )  = (stage2 rinvOL2' (codeLift2 rinvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      linvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      rinvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))