
 module MoufangLoop  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MoufangLoop (A  : Set )  : Set where
    constructor MoufangLoopC
    field
      op : (A  → (A  → A ))
      e : A 
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      linv : (A  → (A  → A ))
      leftCancel : ({x y  : A }  → (op x (linv x y ) ) ≡ y )
      lefCancelOp : ({x y  : A }  → (linv x (op x y ) ) ≡ y )
      rinv : (A  → (A  → A ))
      rightCancel : ({x y  : A }  → (op (rinv y x ) x ) ≡ y )
      rightCancelOp : ({x y  : A }  → (rinv (op y x ) x ) ≡ y )
      moufangId : ({x y z  : A }  → (op (op z x ) (op y z ) ) ≡ (op (op z (op x y ) ) z )) 
  
  open MoufangLoop
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS 
      linvS : (AS  → (AS  → AS ))
      rinvS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      linvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      rinvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP )
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      leftCancelP : ({xP yP  : (Prod AP AP )}  → (opP xP (linvP xP yP ) ) ≡ yP )
      lefCancelOpP : ({xP yP  : (Prod AP AP )}  → (linvP xP (opP xP yP ) ) ≡ yP )
      rightCancelP : ({xP yP  : (Prod AP AP )}  → (opP (rinvP yP xP ) xP ) ≡ yP )
      rightCancelOpP : ({xP yP  : (Prod AP AP )}  → (rinvP (opP yP xP ) xP ) ≡ yP )
      moufangIdP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP zP xP ) (opP yP zP ) ) ≡ (opP (opP zP (opP xP yP ) ) zP )) 
  
  record Hom (A1 A2  : Set ) (Mo1  : (MoufangLoop A1 )) (Mo2  : (MoufangLoop A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mo1 ) x1 x2 ) ) ≡ ((op Mo2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Mo1 )  ) ≡ (e Mo2 ) )
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Mo1 ) x1 x2 ) ) ≡ ((linv Mo2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Mo1 ) x1 x2 ) ) ≡ ((rinv Mo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mo1  : (MoufangLoop A1 )) (Mo2  : (MoufangLoop A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mo1 ) x1 x2 ) ((op Mo2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Mo1 )  (e Mo2 )  ))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Mo1 ) x1 x2 ) ((linv Mo2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Mo1 ) x1 x2 ) ((rinv Mo2 ) y1 y2 ) )))) 
  
  data MoufangLoopLTerm  : Set where
    opL : (MoufangLoopLTerm   → (MoufangLoopLTerm   → MoufangLoopLTerm  ))
    eL : MoufangLoopLTerm  
    linvL : (MoufangLoopLTerm   → (MoufangLoopLTerm   → MoufangLoopLTerm  ))
    rinvL : (MoufangLoopLTerm   → (MoufangLoopLTerm   → MoufangLoopLTerm  )) 
  
  data ClMoufangLoopClTerm (A  : Set )  : Set where
    sing : (A  → (ClMoufangLoopClTerm A ) )
    opCl : ((ClMoufangLoopClTerm A )  → ((ClMoufangLoopClTerm A )  → (ClMoufangLoopClTerm A ) ))
    eCl : (ClMoufangLoopClTerm A ) 
    linvCl : ((ClMoufangLoopClTerm A )  → ((ClMoufangLoopClTerm A )  → (ClMoufangLoopClTerm A ) ))
    rinvCl : ((ClMoufangLoopClTerm A )  → ((ClMoufangLoopClTerm A )  → (ClMoufangLoopClTerm A ) )) 
  
  data OpMoufangLoopOLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMoufangLoopOLTerm n ) )
    opOL : ((OpMoufangLoopOLTerm n )  → ((OpMoufangLoopOLTerm n )  → (OpMoufangLoopOLTerm n ) ))
    eOL : (OpMoufangLoopOLTerm n ) 
    linvOL : ((OpMoufangLoopOLTerm n )  → ((OpMoufangLoopOLTerm n )  → (OpMoufangLoopOLTerm n ) ))
    rinvOL : ((OpMoufangLoopOLTerm n )  → ((OpMoufangLoopOLTerm n )  → (OpMoufangLoopOLTerm n ) )) 
  
  data OpMoufangLoopOL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMoufangLoopOL2Term2 n A ) )
    sing2 : (A  → (OpMoufangLoopOL2Term2 n A ) )
    opOL2 : ((OpMoufangLoopOL2Term2 n A )  → ((OpMoufangLoopOL2Term2 n A )  → (OpMoufangLoopOL2Term2 n A ) ))
    eOL2 : (OpMoufangLoopOL2Term2 n A ) 
    linvOL2 : ((OpMoufangLoopOL2Term2 n A )  → ((OpMoufangLoopOL2Term2 n A )  → (OpMoufangLoopOL2Term2 n A ) ))
    rinvOL2 : ((OpMoufangLoopOL2Term2 n A )  → ((OpMoufangLoopOL2Term2 n A )  → (OpMoufangLoopOL2Term2 n A ) )) 
  
  simplifyB : (MoufangLoopLTerm  → MoufangLoopLTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB (opL x eL )  = x 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB eL  = eL 
  
  simplifyB (linvL x1 x2 )  = (linvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (rinvL x1 x2 )  = (rinvL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMoufangLoopClTerm A ) → (ClMoufangLoopClTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ (opCl x eCl )  = x 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (linvCl x1 x2 )  = (linvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (rinvCl x1 x2 )  = (rinvCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMoufangLoopOLTerm n ) → (OpMoufangLoopOLTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ (opOL x eOL )  = x 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (linvOL x1 x2 )  = (linvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (rinvOL x1 x2 )  = (rinvOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMoufangLoopOL2Term2 n A ) → (OpMoufangLoopOL2Term2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x eOL2 )  = x 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (linvOL2 x1 x2 )  = (linvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (rinvOL2 x1 x2 )  = (rinvOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MoufangLoop A ) → (MoufangLoopLTerm  → A )))
  evalB Mo (opL x1 x2 )  = ((op Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalB Mo eL  = (e Mo ) 
  
  evalB Mo (linvL x1 x2 )  = ((linv Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalB Mo (rinvL x1 x2 )  = ((rinv Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalCl : ({A  : Set }  → ((MoufangLoop A ) → ((ClMoufangLoopClTerm A ) → A )))
  evalCl Mo (sing x1 )  = x1 
  
  evalCl Mo (opCl x1 x2 )  = ((op Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalCl Mo eCl  = (e Mo ) 
  
  evalCl Mo (linvCl x1 x2 )  = ((linv Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalCl Mo (rinvCl x1 x2 )  = ((rinv Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MoufangLoop A ) → ((Vec A n ) → ((OpMoufangLoopOLTerm n ) → A ))))
  evalOp n Mo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mo vars (opOL x1 x2 )  = ((op Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOp n Mo vars eOL  = (e Mo ) 
  
  evalOp n Mo vars (linvOL x1 x2 )  = ((linv Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOp n Mo vars (rinvOL x1 x2 )  = ((rinv Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MoufangLoop A ) → ((Vec A n ) → ((OpMoufangLoopOL2Term2 n A ) → A ))))
  evalOpE n Mo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mo vars (sing2 x1 )  = x1 
  
  evalOpE n Mo vars (opOL2 x1 x2 )  = ((op Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  evalOpE n Mo vars eOL2  = (e Mo ) 
  
  evalOpE n Mo vars (linvOL2 x1 x2 )  = ((linv Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  evalOpE n Mo vars (rinvOL2 x1 x2 )  = ((rinv Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  inductionB : ((P  : (MoufangLoopLTerm  → Set ))  → (((x1 x2  : MoufangLoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → (((x1 x2  : MoufangLoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → (((x1 x2  : MoufangLoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : MoufangLoopLTerm )  → (P x )))))))
  inductionB p popl pel plinvl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl pel plinvl prinvl x1 ) (inductionB p popl pel plinvl prinvl x2 ) )
  
  inductionB p popl pel plinvl prinvl eL  = pel 
  
  inductionB p popl pel plinvl prinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl pel plinvl prinvl x1 ) (inductionB p popl pel plinvl prinvl x2 ) )
  
  inductionB p popl pel plinvl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl pel plinvl prinvl x1 ) (inductionB p popl pel plinvl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMoufangLoopClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMoufangLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → (((x1 x2  : (ClMoufangLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → (((x1 x2  : (ClMoufangLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClMoufangLoopClTerm A ))  → (P x ))))))))
  inductionCl _ p psing popcl pecl plinvcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl eCl  = pecl 
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMoufangLoopOLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMoufangLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → (((x1 x2  : (OpMoufangLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → (((x1 x2  : (OpMoufangLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpMoufangLoopOLTerm n ))  → (P x ))))))))
  inductionOp _ p pv popol peol plinvol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol plinvol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol plinvol prinvol x1 ) (inductionOp _ p pv popol peol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol peol plinvol prinvol eOL  = peol 
  
  inductionOp _ p pv popol peol plinvol prinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol peol plinvol prinvol x1 ) (inductionOp _ p pv popol peol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol peol plinvol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol peol plinvol prinvol x1 ) (inductionOp _ p pv popol peol plinvol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMoufangLoopOL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMoufangLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → (((x1 x2  : (OpMoufangLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → (((x1 x2  : (OpMoufangLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpMoufangLoopOL2Term2 n A ))  → (P x )))))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2 ) )
  
  opL' : (  (MoufangLoopLTerm   → (MoufangLoopLTerm   → MoufangLoopLTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  MoufangLoopLTerm  )
  eL'  = eL 
  
  linvL' : (  (MoufangLoopLTerm   → (MoufangLoopLTerm   → MoufangLoopLTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  rinvL' : (  (MoufangLoopLTerm   → (MoufangLoopLTerm   → MoufangLoopLTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (MoufangLoopLTerm  → (Staged MoufangLoopLTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMoufangLoopClTerm A )  → ((ClMoufangLoopClTerm A )  → (ClMoufangLoopClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClMoufangLoopClTerm A ) )
  eCl'  = eCl 
  
  linvCl' : ({A  : Set }  → ((ClMoufangLoopClTerm A )  → ((ClMoufangLoopClTerm A )  → (ClMoufangLoopClTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClMoufangLoopClTerm A )  → ((ClMoufangLoopClTerm A )  → (ClMoufangLoopClTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMoufangLoopClTerm A ) → (Staged (ClMoufangLoopClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMoufangLoopOLTerm n )  → ((OpMoufangLoopOLTerm n )  → (OpMoufangLoopOLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpMoufangLoopOLTerm n ) )
  eOL'  = eOL 
  
  linvOL' : ({n  : Nat}  → ((OpMoufangLoopOLTerm n )  → ((OpMoufangLoopOLTerm n )  → (OpMoufangLoopOLTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpMoufangLoopOLTerm n )  → ((OpMoufangLoopOLTerm n )  → (OpMoufangLoopOLTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMoufangLoopOLTerm n ) → (Staged (OpMoufangLoopOLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangLoopOL2Term2 n A )  → ((OpMoufangLoopOL2Term2 n A )  → (OpMoufangLoopOL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpMoufangLoopOL2Term2 n A ) )
  eOL2'  = eOL2 
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangLoopOL2Term2 n A )  → ((OpMoufangLoopOL2Term2 n A )  → (OpMoufangLoopOL2Term2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangLoopOL2Term2 n A )  → ((OpMoufangLoopOL2Term2 n A )  → (OpMoufangLoopOL2Term2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMoufangLoopOL2Term2 n A ) → (Staged (OpMoufangLoopOL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (linvOL2 x1 x2 )  = (stage2 linvOL2' (codeLift2 linvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (rinvOL2 x1 x2 )  = (stage2 rinvOL2' (codeLift2 rinvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 
      linvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      rinvT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
