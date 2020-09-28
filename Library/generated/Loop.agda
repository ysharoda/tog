module Loop  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Loop (A  : Set )  : Set where
    constructor LoopC
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
  open Loop
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
  record Hom (A1 A2  : Set ) (Lo1  : (Loop A1 )) (Lo2  : (Loop A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Lo1 ) x1 x2 ) ) ≡ ((op Lo2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Lo1 )  ) ≡ (e Lo2 ) )
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Lo1 ) x1 x2 ) ) ≡ ((linv Lo2 ) (hom x1 ) (hom x2 ) ))
      pres-rinv : ({x1  : A1} {x2  : A1}  → (hom ((rinv Lo1 ) x1 x2 ) ) ≡ ((rinv Lo2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Lo1  : (Loop A1 )) (Lo2  : (Loop A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Lo1 ) x1 x2 ) ((op Lo2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Lo1 )  (e Lo2 )  ))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Lo1 ) x1 x2 ) ((linv Lo2 ) y1 y2 ) ))))
      interp-rinv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((rinv Lo1 ) x1 x2 ) ((rinv Lo2 ) y1 y2 ) ))))
  data LoopLTerm  : Set where
    opL : (LoopLTerm   → (LoopLTerm   → LoopLTerm  ))
    eL : LoopLTerm  
    linvL : (LoopLTerm   → (LoopLTerm   → LoopLTerm  ))
    rinvL : (LoopLTerm   → (LoopLTerm   → LoopLTerm  ))
  data ClLoopClTerm (A  : Set )  : Set where
    sing : (A  → (ClLoopClTerm A ) )
    opCl : ((ClLoopClTerm A )  → ((ClLoopClTerm A )  → (ClLoopClTerm A ) ))
    eCl : (ClLoopClTerm A ) 
    linvCl : ((ClLoopClTerm A )  → ((ClLoopClTerm A )  → (ClLoopClTerm A ) ))
    rinvCl : ((ClLoopClTerm A )  → ((ClLoopClTerm A )  → (ClLoopClTerm A ) ))
  data OpLoopOLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLoopOLTerm n ) )
    opOL : ((OpLoopOLTerm n )  → ((OpLoopOLTerm n )  → (OpLoopOLTerm n ) ))
    eOL : (OpLoopOLTerm n ) 
    linvOL : ((OpLoopOLTerm n )  → ((OpLoopOLTerm n )  → (OpLoopOLTerm n ) ))
    rinvOL : ((OpLoopOLTerm n )  → ((OpLoopOLTerm n )  → (OpLoopOLTerm n ) ))
  data OpLoopOL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLoopOL2Term2 n A ) )
    sing2 : (A  → (OpLoopOL2Term2 n A ) )
    opOL2 : ((OpLoopOL2Term2 n A )  → ((OpLoopOL2Term2 n A )  → (OpLoopOL2Term2 n A ) ))
    eOL2 : (OpLoopOL2Term2 n A ) 
    linvOL2 : ((OpLoopOL2Term2 n A )  → ((OpLoopOL2Term2 n A )  → (OpLoopOL2Term2 n A ) ))
    rinvOL2 : ((OpLoopOL2Term2 n A )  → ((OpLoopOL2Term2 n A )  → (OpLoopOL2Term2 n A ) ))
  evalB : ({A  : Set }  → ((Loop A ) → (LoopLTerm  → A )))
  evalB Lo (opL x1 x2 )  = ((op Lo ) (evalB Lo x1 ) (evalB Lo x2 ) )
  
  evalB Lo eL  = (e Lo ) 
  
  evalB Lo (linvL x1 x2 )  = ((linv Lo ) (evalB Lo x1 ) (evalB Lo x2 ) )
  
  evalB Lo (rinvL x1 x2 )  = ((rinv Lo ) (evalB Lo x1 ) (evalB Lo x2 ) )
  
  evalCl : ({A  : Set }  → ((Loop A ) → ((ClLoopClTerm A ) → A )))
  evalCl Lo (sing x1 )  = x1 
  
  evalCl Lo (opCl x1 x2 )  = ((op Lo ) (evalCl Lo x1 ) (evalCl Lo x2 ) )
  
  evalCl Lo eCl  = (e Lo ) 
  
  evalCl Lo (linvCl x1 x2 )  = ((linv Lo ) (evalCl Lo x1 ) (evalCl Lo x2 ) )
  
  evalCl Lo (rinvCl x1 x2 )  = ((rinv Lo ) (evalCl Lo x1 ) (evalCl Lo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Loop A ) → ((Vec A n ) → ((OpLoopOLTerm n ) → A ))))
  evalOp n Lo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Lo vars (opOL x1 x2 )  = ((op Lo ) (evalOp n Lo vars x1 ) (evalOp n Lo vars x2 ) )
  
  evalOp n Lo vars eOL  = (e Lo ) 
  
  evalOp n Lo vars (linvOL x1 x2 )  = ((linv Lo ) (evalOp n Lo vars x1 ) (evalOp n Lo vars x2 ) )
  
  evalOp n Lo vars (rinvOL x1 x2 )  = ((rinv Lo ) (evalOp n Lo vars x1 ) (evalOp n Lo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Loop A ) → ((Vec A n ) → ((OpLoopOL2Term2 n A ) → A ))))
  evalOpE n Lo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Lo vars (sing2 x1 )  = x1 
  
  evalOpE n Lo vars (opOL2 x1 x2 )  = ((op Lo ) (evalOpE n Lo vars x1 ) (evalOpE n Lo vars x2 ) )
  
  evalOpE n Lo vars eOL2  = (e Lo ) 
  
  evalOpE n Lo vars (linvOL2 x1 x2 )  = ((linv Lo ) (evalOpE n Lo vars x1 ) (evalOpE n Lo vars x2 ) )
  
  evalOpE n Lo vars (rinvOL2 x1 x2 )  = ((rinv Lo ) (evalOpE n Lo vars x1 ) (evalOpE n Lo vars x2 ) )
  
  inductionB : ((P  : (LoopLTerm  → Set ))  → (((x1 x2  : LoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → (((x1 x2  : LoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → (((x1 x2  : LoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (rinvL x1 x2 ) )))) → ((x  : LoopLTerm )  → (P x )))))))
  inductionB p popl pel plinvl prinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl pel plinvl prinvl x1 ) (inductionB p popl pel plinvl prinvl x2 ) )
  
  inductionB p popl pel plinvl prinvl eL  = pel 
  
  inductionB p popl pel plinvl prinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl pel plinvl prinvl x1 ) (inductionB p popl pel plinvl prinvl x2 ) )
  
  inductionB p popl pel plinvl prinvl (rinvL x1 x2 )  = (prinvl _ _ (inductionB p popl pel plinvl prinvl x1 ) (inductionB p popl pel plinvl prinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLoopClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → (((x1 x2  : (ClLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → (((x1 x2  : (ClLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvCl x1 x2 ) )))) → ((x  : (ClLoopClTerm A ))  → (P x ))))))))
  inductionCl _ p psing popcl pecl plinvcl prinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl eCl  = pecl 
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2 ) )
  
  inductionCl _ p psing popcl pecl plinvcl prinvcl (rinvCl x1 x2 )  = (prinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl prinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl prinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLoopOLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → (((x1 x2  : (OpLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → (((x1 x2  : (OpLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL x1 x2 ) )))) → ((x  : (OpLoopOLTerm n ))  → (P x ))))))))
  inductionOp _ p pv popol peol plinvol prinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol plinvol prinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol plinvol prinvol x1 ) (inductionOp _ p pv popol peol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol peol plinvol prinvol eOL  = peol 
  
  inductionOp _ p pv popol peol plinvol prinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol peol plinvol prinvol x1 ) (inductionOp _ p pv popol peol plinvol prinvol x2 ) )
  
  inductionOp _ p pv popol peol plinvol prinvol (rinvOL x1 x2 )  = (prinvol _ _ (inductionOp _ p pv popol peol plinvol prinvol x1 ) (inductionOp _ p pv popol peol plinvol prinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLoopOL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → (((x1 x2  : (OpLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → (((x1 x2  : (OpLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (rinvOL2 x1 x2 ) )))) → ((x  : (OpLoopOL2Term2 n A ))  → (P x )))))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 (rinvOL2 x1 x2 )  = (prinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 prinvol2 x2 ) )
  
  opL' : (  (LoopLTerm   → (LoopLTerm   → LoopLTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  LoopLTerm  )
  eL'  = eL 
  
  linvL' : (  (LoopLTerm   → (LoopLTerm   → LoopLTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  rinvL' : (  (LoopLTerm   → (LoopLTerm   → LoopLTerm  )))
  rinvL' x1 x2  = (rinvL x1 x2 )
  
  stageB : (LoopLTerm  → (Staged LoopLTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (rinvL x1 x2 )  = (stage2 rinvL' (codeLift2 rinvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClLoopClTerm A )  → ((ClLoopClTerm A )  → (ClLoopClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClLoopClTerm A ) )
  eCl'  = eCl 
  
  linvCl' : ({A  : Set }  → ((ClLoopClTerm A )  → ((ClLoopClTerm A )  → (ClLoopClTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  rinvCl' : ({A  : Set }  → ((ClLoopClTerm A )  → ((ClLoopClTerm A )  → (ClLoopClTerm A ) )))
  rinvCl' x1 x2  = (rinvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLoopClTerm A ) → (Staged (ClLoopClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (rinvCl x1 x2 )  = (stage2 rinvCl' (codeLift2 rinvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpLoopOLTerm n )  → ((OpLoopOLTerm n )  → (OpLoopOLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpLoopOLTerm n ) )
  eOL'  = eOL 
  
  linvOL' : ({n  : Nat}  → ((OpLoopOLTerm n )  → ((OpLoopOLTerm n )  → (OpLoopOLTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  rinvOL' : ({n  : Nat}  → ((OpLoopOLTerm n )  → ((OpLoopOLTerm n )  → (OpLoopOLTerm n ) )))
  rinvOL' x1 x2  = (rinvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLoopOLTerm n ) → (Staged (OpLoopOLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (rinvOL x1 x2 )  = (stage2 rinvOL' (codeLift2 rinvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLoopOL2Term2 n A )  → ((OpLoopOL2Term2 n A )  → (OpLoopOL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpLoopOL2Term2 n A ) )
  eOL2'  = eOL2 
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpLoopOL2Term2 n A )  → ((OpLoopOL2Term2 n A )  → (OpLoopOL2Term2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  rinvOL2' : ({n  : Nat } {A  : Set }  → ((OpLoopOL2Term2 n A )  → ((OpLoopOL2Term2 n A )  → (OpLoopOL2Term2 n A ) )))
  rinvOL2' x1 x2  = (rinvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLoopOL2Term2 n A ) → (Staged (OpLoopOL2Term2 n A ) )))
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