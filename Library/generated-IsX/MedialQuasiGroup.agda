
 module MedialQuasiGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMedialQuasiGroup (A  : Set ) (op  : (A  → (A  → A ))) (linv  : (A  → (A  → A ))) (rinv  : (A  → (A  → A )))  : Set where
    constructor IsMedialQuasiGroupC
    field
      leftCancel : ({x y  : A }  → (op x (linv x y ) ) ≡ y )
      lefCancelOp : ({x y  : A }  → (linv x (op x y ) ) ≡ y )
      rightCancel : ({x y  : A }  → (op (rinv y x ) x ) ≡ y )
      rightCancelOp : ({x y  : A }  → (rinv (op y x ) x ) ≡ y )
      mediates : ({w x y z  : A }  → (op (op x y ) (op z w ) ) ≡ (op (op x z ) (op y w ) )) 
  
  record MedialQuasiGroup (A  : Set )  : Set where
    constructor MedialQuasiGroupC
    field
      op : (A  → (A  → A ))
      linv : (A  → (A  → A ))
      rinv : (A  → (A  → A ))
      isMedialQuasiGroup : (IsMedialQuasiGroup A op linv rinv ) 
  
  open MedialQuasiGroup
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
      mediatesP : ({wP xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) (opP zP wP ) ) ≡ (opP (opP xP zP ) (opP yP wP ) )) 
  
  record Hom (A1 A2  : Set ) (Me1  : (MedialQuasiGroup A1 )) (Me2  : (MedialQuasiGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Me1 ) x1 x2 ) ) ≡ ((op Me2 ) (hom x1 ) (hom x2 ) ))
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Me1 ) x1 x2 ) ) ≡ ((linv Me2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Me1 ) x1 x2 ) ) ≡ ((rinv Me2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Me1  : (MedialQuasiGroup A1 )) (Me2  : (MedialQuasiGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Me1 ) x1 x2 ) ((op Me2 ) y1 y2 ) ))))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Me1 ) x1 x2 ) ((linv Me2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Me1 ) x1 x2 ) ((rinv Me2 ) y1 y2 ) )))) 
  
  data MedialQuasiGroupTerm  : Set where
    opL : (MedialQuasiGroupTerm   → (MedialQuasiGroupTerm   → MedialQuasiGroupTerm  ))
    linvL : (MedialQuasiGroupTerm   → (MedialQuasiGroupTerm   → MedialQuasiGroupTerm  ))
    rinvL : (MedialQuasiGroupTerm   → (MedialQuasiGroupTerm   → MedialQuasiGroupTerm  )) 
  
  data ClMedialQuasiGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClMedialQuasiGroupTerm A ) )
    opCl : ((ClMedialQuasiGroupTerm A )  → ((ClMedialQuasiGroupTerm A )  → (ClMedialQuasiGroupTerm A ) ))
    linvCl : ((ClMedialQuasiGroupTerm A )  → ((ClMedialQuasiGroupTerm A )  → (ClMedialQuasiGroupTerm A ) ))
    rinvCl : ((ClMedialQuasiGroupTerm A )  → ((ClMedialQuasiGroupTerm A )  → (ClMedialQuasiGroupTerm A ) )) 
  
  data OpMedialQuasiGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMedialQuasiGroupTerm n ) )
    opOL : ((OpMedialQuasiGroupTerm n )  → ((OpMedialQuasiGroupTerm n )  → (OpMedialQuasiGroupTerm n ) ))
    linvOL : ((OpMedialQuasiGroupTerm n )  → ((OpMedialQuasiGroupTerm n )  → (OpMedialQuasiGroupTerm n ) ))
    rinvOL : ((OpMedialQuasiGroupTerm n )  → ((OpMedialQuasiGroupTerm n )  → (OpMedialQuasiGroupTerm n ) )) 
  
  data OpMedialQuasiGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMedialQuasiGroupTerm2 n A ) )
    sing2 : (A  → (OpMedialQuasiGroupTerm2 n A ) )
    opOL2 : ((OpMedialQuasiGroupTerm2 n A )  → ((OpMedialQuasiGroupTerm2 n A )  → (OpMedialQuasiGroupTerm2 n A ) ))
    linvOL2 : ((OpMedialQuasiGroupTerm2 n A )  → ((OpMedialQuasiGroupTerm2 n A )  → (OpMedialQuasiGroupTerm2 n A ) ))
    rinvOL2 : ((OpMedialQuasiGroupTerm2 n A )  → ((OpMedialQuasiGroupTerm2 n A )  → (OpMedialQuasiGroupTerm2 n A ) )) 
  
  simplifyB : (MedialQuasiGroupTerm  → MedialQuasiGroupTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (linvL x1 x2 )  = (linvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (rinvL x1 x2 )  = (rinvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMedialQuasiGroupTerm A ) → (ClMedialQuasiGroupTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (linvCl x1 x2 )  = (linvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (rinvCl x1 x2 )  = (rinvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMedialQuasiGroupTerm n ) → (OpMedialQuasiGroupTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (linvOL x1 x2 )  = (linvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (rinvOL x1 x2 )  = (rinvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMedialQuasiGroupTerm2 n A ) → (OpMedialQuasiGroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (linvOL2 x1 x2 )  = (linvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (rinvOL2 x1 x2 )  = (rinvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MedialQuasiGroup A ) → (MedialQuasiGroupTerm  → A )))
  evalB Me (opL x1 x2 )  = ((op Me ) (evalB Me x1 ) (evalB Me x2 ) )
  
  evalB Me (linvL x1 x2 )  = ((linv Me ) (evalB Me x1 ) (evalB Me x2 ) )
  
  evalB Me (rinvL x1 x2 )  = ((rinv Me ) (evalB Me x1 ) (evalB Me x2 ) )
  
  evalCl : ({A  : Set }  → ((MedialQuasiGroup A ) → ((ClMedialQuasiGroupTerm A ) → A )))
  evalCl Me (sing x1 )  = x1 
  
  evalCl Me (opCl x1 x2 )  = ((op Me ) (evalCl Me x1 ) (evalCl Me x2 ) )
  
  evalCl Me (linvCl x1 x2 )  = ((linv Me ) (evalCl Me x1 ) (evalCl Me x2 ) )
  
  evalCl Me (rinvCl x1 x2 )  = ((rinv Me ) (evalCl Me x1 ) (evalCl Me x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MedialQuasiGroup A ) → ((Vec A n ) → ((OpMedialQuasiGroupTerm n ) → A ))))
  evalOp n Me vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Me vars (opOL x1 x2 )  = ((op Me ) (evalOp n Me vars x1 ) (evalOp n Me vars x2 ) )
  
  evalOp n Me vars (linvOL x1 x2 )  = ((linv Me ) (evalOp n Me vars x1 ) (evalOp n Me vars x2 ) )
  
  evalOp n Me vars (rinvOL x1 x2 )  = ((rinv Me ) (evalOp n Me vars x1 ) (evalOp n Me vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MedialQuasiGroup A ) → ((Vec A n ) → ((OpMedialQuasiGroupTerm2 n A ) → A ))))
  evalOpE n Me vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Me vars (sing2 x1 )  = x1 
  
  evalOpE n Me vars (opOL2 x1 x2 )  = ((op Me ) (evalOpE n Me vars x1 ) (evalOpE n Me vars x2 ) )
  
  evalOpE n Me vars (linvOL2 x1 x2 )  = ((linv Me ) (evalOpE n Me vars x1 ) (evalOpE n Me vars x2 ) )
  
  evalOpE n Me vars (rinvOL2 x1 x2 )  = ((rinv Me ) (evalOpE n Me vars x1 ) (evalOpE n Me vars x2 ) )
  
  inductionB : ((P  : (MedialQuasiGroupTerm  → Set ))  → (((x1 x2  : MedialQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : MedialQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → (((x1 x2  : MedialQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : MedialQuasiGroupTerm )  → (P x ))))))
  inductionB p popl plinvl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionB p popl plinvl prinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionB p popl plinvl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMedialQuasiGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMedialQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClMedialQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → (((x1 x2  : (ClMedialQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClMedialQuasiGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl plinvcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl plinvcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl prinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMedialQuasiGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMedialQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpMedialQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → (((x1 x2  : (OpMedialQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpMedialQuasiGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv popol plinvol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol plinvol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol plinvol prinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol plinvol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMedialQuasiGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMedialQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpMedialQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → (((x1 x2  : (OpMedialQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpMedialQuasiGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  opL' : (  (MedialQuasiGroupTerm   → (MedialQuasiGroupTerm   → MedialQuasiGroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  linvL' : (  (MedialQuasiGroupTerm   → (MedialQuasiGroupTerm   → MedialQuasiGroupTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  rinvL' : (  (MedialQuasiGroupTerm   → (MedialQuasiGroupTerm   → MedialQuasiGroupTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (MedialQuasiGroupTerm  → (Staged MedialQuasiGroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMedialQuasiGroupTerm A )  → ((ClMedialQuasiGroupTerm A )  → (ClMedialQuasiGroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  linvCl' : ({A  : Set }  → ((ClMedialQuasiGroupTerm A )  → ((ClMedialQuasiGroupTerm A )  → (ClMedialQuasiGroupTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClMedialQuasiGroupTerm A )  → ((ClMedialQuasiGroupTerm A )  → (ClMedialQuasiGroupTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMedialQuasiGroupTerm A ) → (Staged (ClMedialQuasiGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMedialQuasiGroupTerm n )  → ((OpMedialQuasiGroupTerm n )  → (OpMedialQuasiGroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  linvOL' : ({n  : Nat}  → ((OpMedialQuasiGroupTerm n )  → ((OpMedialQuasiGroupTerm n )  → (OpMedialQuasiGroupTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpMedialQuasiGroupTerm n )  → ((OpMedialQuasiGroupTerm n )  → (OpMedialQuasiGroupTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMedialQuasiGroupTerm n ) → (Staged (OpMedialQuasiGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMedialQuasiGroupTerm2 n A )  → ((OpMedialQuasiGroupTerm2 n A )  → (OpMedialQuasiGroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpMedialQuasiGroupTerm2 n A )  → ((OpMedialQuasiGroupTerm2 n A )  → (OpMedialQuasiGroupTerm2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpMedialQuasiGroupTerm2 n A )  → ((OpMedialQuasiGroupTerm2 n A )  → (OpMedialQuasiGroupTerm2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMedialQuasiGroupTerm2 n A ) → (Staged (OpMedialQuasiGroupTerm2 n A ) )))
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
   
