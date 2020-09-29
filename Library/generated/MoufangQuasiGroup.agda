
 module MoufangQuasiGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MoufangQuasiGroup (A  : Set )  : Set where
    constructor MoufangQuasiGroupC
    field
      op : (A  → (A  → A ))
      linv : (A  → (A  → A ))
      leftCancel : ({x y  : A }  → (op x (linv x y ) ) ≡ y )
      lefCancelOp : ({x y  : A }  → (linv x (op x y ) ) ≡ y )
      rinv : (A  → (A  → A ))
      rightCancel : ({x y  : A }  → (op (rinv y x ) x ) ≡ y )
      rightCancelOp : ({x y  : A }  → (rinv (op y x ) x ) ≡ y )
      moufangLaw : ({e x y z  : A }  → ((op y e )  ≡ y  → (op (op (op x y ) z ) x ) ≡ (op x (op y (op (op e z ) x ) ) ))) 
  
  open MoufangQuasiGroup
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
      moufangLawP : ({eP xP yP zP  : (Prod AP AP )}  → ((opP yP eP )  ≡ yP  → (opP (opP (opP xP yP ) zP ) xP ) ≡ (opP xP (opP yP (opP (opP eP zP ) xP ) ) ))) 
  
  record Hom (A1 A2  : Set ) (Mo1  : (MoufangQuasiGroup A1 )) (Mo2  : (MoufangQuasiGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mo1 ) x1 x2 ) ) ≡ ((op Mo2 ) (hom x1 ) (hom x2 ) ))
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Mo1 ) x1 x2 ) ) ≡ ((linv Mo2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Mo1 ) x1 x2 ) ) ≡ ((rinv Mo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mo1  : (MoufangQuasiGroup A1 )) (Mo2  : (MoufangQuasiGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mo1 ) x1 x2 ) ((op Mo2 ) y1 y2 ) ))))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Mo1 ) x1 x2 ) ((linv Mo2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Mo1 ) x1 x2 ) ((rinv Mo2 ) y1 y2 ) )))) 
  
  data MoufangQuasiGroupTerm  : Set where
    opL : (MoufangQuasiGroupTerm   → (MoufangQuasiGroupTerm   → MoufangQuasiGroupTerm  ))
    linvL : (MoufangQuasiGroupTerm   → (MoufangQuasiGroupTerm   → MoufangQuasiGroupTerm  ))
    rinvL : (MoufangQuasiGroupTerm   → (MoufangQuasiGroupTerm   → MoufangQuasiGroupTerm  )) 
  
  data ClMoufangQuasiGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClMoufangQuasiGroupTerm A ) )
    opCl : ((ClMoufangQuasiGroupTerm A )  → ((ClMoufangQuasiGroupTerm A )  → (ClMoufangQuasiGroupTerm A ) ))
    linvCl : ((ClMoufangQuasiGroupTerm A )  → ((ClMoufangQuasiGroupTerm A )  → (ClMoufangQuasiGroupTerm A ) ))
    rinvCl : ((ClMoufangQuasiGroupTerm A )  → ((ClMoufangQuasiGroupTerm A )  → (ClMoufangQuasiGroupTerm A ) )) 
  
  data OpMoufangQuasiGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMoufangQuasiGroupTerm n ) )
    opOL : ((OpMoufangQuasiGroupTerm n )  → ((OpMoufangQuasiGroupTerm n )  → (OpMoufangQuasiGroupTerm n ) ))
    linvOL : ((OpMoufangQuasiGroupTerm n )  → ((OpMoufangQuasiGroupTerm n )  → (OpMoufangQuasiGroupTerm n ) ))
    rinvOL : ((OpMoufangQuasiGroupTerm n )  → ((OpMoufangQuasiGroupTerm n )  → (OpMoufangQuasiGroupTerm n ) )) 
  
  data OpMoufangQuasiGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMoufangQuasiGroupTerm2 n A ) )
    sing2 : (A  → (OpMoufangQuasiGroupTerm2 n A ) )
    opOL2 : ((OpMoufangQuasiGroupTerm2 n A )  → ((OpMoufangQuasiGroupTerm2 n A )  → (OpMoufangQuasiGroupTerm2 n A ) ))
    linvOL2 : ((OpMoufangQuasiGroupTerm2 n A )  → ((OpMoufangQuasiGroupTerm2 n A )  → (OpMoufangQuasiGroupTerm2 n A ) ))
    rinvOL2 : ((OpMoufangQuasiGroupTerm2 n A )  → ((OpMoufangQuasiGroupTerm2 n A )  → (OpMoufangQuasiGroupTerm2 n A ) )) 
  
  simplifyB : (MoufangQuasiGroupTerm  → MoufangQuasiGroupTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (linvL x1 x2 )  = (linvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (rinvL x1 x2 )  = (rinvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMoufangQuasiGroupTerm A ) → (ClMoufangQuasiGroupTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (linvCl x1 x2 )  = (linvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (rinvCl x1 x2 )  = (rinvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMoufangQuasiGroupTerm n ) → (OpMoufangQuasiGroupTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (linvOL x1 x2 )  = (linvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (rinvOL x1 x2 )  = (rinvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMoufangQuasiGroupTerm2 n A ) → (OpMoufangQuasiGroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (linvOL2 x1 x2 )  = (linvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (rinvOL2 x1 x2 )  = (rinvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MoufangQuasiGroup A ) → (MoufangQuasiGroupTerm  → A )))
  evalB Mo (opL x1 x2 )  = ((op Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalB Mo (linvL x1 x2 )  = ((linv Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalB Mo (rinvL x1 x2 )  = ((rinv Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalCl : ({A  : Set }  → ((MoufangQuasiGroup A ) → ((ClMoufangQuasiGroupTerm A ) → A )))
  evalCl Mo (sing x1 )  = x1 
  
  evalCl Mo (opCl x1 x2 )  = ((op Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalCl Mo (linvCl x1 x2 )  = ((linv Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalCl Mo (rinvCl x1 x2 )  = ((rinv Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MoufangQuasiGroup A ) → ((Vec A n ) → ((OpMoufangQuasiGroupTerm n ) → A ))))
  evalOp n Mo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mo vars (opOL x1 x2 )  = ((op Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOp n Mo vars (linvOL x1 x2 )  = ((linv Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOp n Mo vars (rinvOL x1 x2 )  = ((rinv Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MoufangQuasiGroup A ) → ((Vec A n ) → ((OpMoufangQuasiGroupTerm2 n A ) → A ))))
  evalOpE n Mo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mo vars (sing2 x1 )  = x1 
  
  evalOpE n Mo vars (opOL2 x1 x2 )  = ((op Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  evalOpE n Mo vars (linvOL2 x1 x2 )  = ((linv Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  evalOpE n Mo vars (rinvOL2 x1 x2 )  = ((rinv Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  inductionB : ((P  : (MoufangQuasiGroupTerm  → Set ))  → (((x1 x2  : MoufangQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : MoufangQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → (((x1 x2  : MoufangQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : MoufangQuasiGroupTerm )  → (P x ))))))
  inductionB p popl plinvl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionB p popl plinvl prinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionB p popl plinvl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl plinvl prinvl x1 ) (inductionB p popl plinvl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMoufangQuasiGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMoufangQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClMoufangQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → (((x1 x2  : (ClMoufangQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClMoufangQuasiGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl plinvcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl plinvcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl prinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl plinvcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMoufangQuasiGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMoufangQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpMoufangQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → (((x1 x2  : (OpMoufangQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpMoufangQuasiGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv popol plinvol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol plinvol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol plinvol prinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol plinvol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol plinvol prinvol x1 ) (inductionOp _ p pv popol plinvol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMoufangQuasiGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMoufangQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpMoufangQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → (((x1 x2  : (OpMoufangQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpMoufangQuasiGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 prinvol2 x2 ) )
  
  opL' : (  (MoufangQuasiGroupTerm   → (MoufangQuasiGroupTerm   → MoufangQuasiGroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  linvL' : (  (MoufangQuasiGroupTerm   → (MoufangQuasiGroupTerm   → MoufangQuasiGroupTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  rinvL' : (  (MoufangQuasiGroupTerm   → (MoufangQuasiGroupTerm   → MoufangQuasiGroupTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (MoufangQuasiGroupTerm  → (Staged MoufangQuasiGroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMoufangQuasiGroupTerm A )  → ((ClMoufangQuasiGroupTerm A )  → (ClMoufangQuasiGroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  linvCl' : ({A  : Set }  → ((ClMoufangQuasiGroupTerm A )  → ((ClMoufangQuasiGroupTerm A )  → (ClMoufangQuasiGroupTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClMoufangQuasiGroupTerm A )  → ((ClMoufangQuasiGroupTerm A )  → (ClMoufangQuasiGroupTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMoufangQuasiGroupTerm A ) → (Staged (ClMoufangQuasiGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMoufangQuasiGroupTerm n )  → ((OpMoufangQuasiGroupTerm n )  → (OpMoufangQuasiGroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  linvOL' : ({n  : Nat}  → ((OpMoufangQuasiGroupTerm n )  → ((OpMoufangQuasiGroupTerm n )  → (OpMoufangQuasiGroupTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpMoufangQuasiGroupTerm n )  → ((OpMoufangQuasiGroupTerm n )  → (OpMoufangQuasiGroupTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMoufangQuasiGroupTerm n ) → (Staged (OpMoufangQuasiGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangQuasiGroupTerm2 n A )  → ((OpMoufangQuasiGroupTerm2 n A )  → (OpMoufangQuasiGroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangQuasiGroupTerm2 n A )  → ((OpMoufangQuasiGroupTerm2 n A )  → (OpMoufangQuasiGroupTerm2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangQuasiGroupTerm2 n A )  → ((OpMoufangQuasiGroupTerm2 n A )  → (OpMoufangQuasiGroupTerm2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMoufangQuasiGroupTerm2 n A ) → (Staged (OpMoufangQuasiGroupTerm2 n A ) )))
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
   
