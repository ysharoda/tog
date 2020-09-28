module LeftLoop  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftLoop (A  : Set )  : Set where
    constructor LeftLoopC
    field
      op : (A  → (A  → A ))
      e : A 
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      linv : (A  → (A  → A ))
      leftCancel : ({x y  : A }  → (op x (linv x y ) ) ≡ y )
      lefCancelOp : ({x y  : A }  → (linv x (op x y ) ) ≡ y )
  open LeftLoop
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS 
      linvS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      linvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      leftCancelP : ({xP yP  : (Prod AP AP )}  → (opP xP (linvP xP yP ) ) ≡ yP )
      lefCancelOpP : ({xP yP  : (Prod AP AP )}  → (linvP xP (opP xP yP ) ) ≡ yP )
  record Hom (A1 A2  : Set ) (Le1  : (LeftLoop A1 )) (Le2  : (LeftLoop A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Le1 ) x1 x2 ) ) ≡ ((op Le2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Le1 )  ) ≡ (e Le2 ) )
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Le1 ) x1 x2 ) ) ≡ ((linv Le2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftLoop A1 )) (Le2  : (LeftLoop A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Le1 ) x1 x2 ) ((op Le2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Le1 )  (e Le2 )  ))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Le1 ) x1 x2 ) ((linv Le2 ) y1 y2 ) ))))
  data LeftLoopLTerm  : Set where
    opL : (LeftLoopLTerm   → (LeftLoopLTerm   → LeftLoopLTerm  ))
    eL : LeftLoopLTerm  
    linvL : (LeftLoopLTerm   → (LeftLoopLTerm   → LeftLoopLTerm  ))
  data ClLeftLoopClTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftLoopClTerm A ) )
    opCl : ((ClLeftLoopClTerm A )  → ((ClLeftLoopClTerm A )  → (ClLeftLoopClTerm A ) ))
    eCl : (ClLeftLoopClTerm A ) 
    linvCl : ((ClLeftLoopClTerm A )  → ((ClLeftLoopClTerm A )  → (ClLeftLoopClTerm A ) ))
  data OpLeftLoopOLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftLoopOLTerm n ) )
    opOL : ((OpLeftLoopOLTerm n )  → ((OpLeftLoopOLTerm n )  → (OpLeftLoopOLTerm n ) ))
    eOL : (OpLeftLoopOLTerm n ) 
    linvOL : ((OpLeftLoopOLTerm n )  → ((OpLeftLoopOLTerm n )  → (OpLeftLoopOLTerm n ) ))
  data OpLeftLoopOL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftLoopOL2Term2 n A ) )
    sing2 : (A  → (OpLeftLoopOL2Term2 n A ) )
    opOL2 : ((OpLeftLoopOL2Term2 n A )  → ((OpLeftLoopOL2Term2 n A )  → (OpLeftLoopOL2Term2 n A ) ))
    eOL2 : (OpLeftLoopOL2Term2 n A ) 
    linvOL2 : ((OpLeftLoopOL2Term2 n A )  → ((OpLeftLoopOL2Term2 n A )  → (OpLeftLoopOL2Term2 n A ) ))
  evalB : ({A  : Set }  → ((LeftLoop A ) → (LeftLoopLTerm  → A )))
  evalB Le (opL x1 x2 )  = ((op Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalB Le eL  = (e Le ) 
  
  evalB Le (linvL x1 x2 )  = ((linv Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftLoop A ) → ((ClLeftLoopClTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (opCl x1 x2 )  = ((op Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalCl Le eCl  = (e Le ) 
  
  evalCl Le (linvCl x1 x2 )  = ((linv Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftLoop A ) → ((Vec A n ) → ((OpLeftLoopOLTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (opOL x1 x2 )  = ((op Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOp n Le vars eOL  = (e Le ) 
  
  evalOp n Le vars (linvOL x1 x2 )  = ((linv Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftLoop A ) → ((Vec A n ) → ((OpLeftLoopOL2Term2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (opOL2 x1 x2 )  = ((op Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  evalOpE n Le vars eOL2  = (e Le ) 
  
  evalOpE n Le vars (linvOL2 x1 x2 )  = ((linv Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftLoopLTerm  → Set ))  → (((x1 x2  : LeftLoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → (((x1 x2  : LeftLoopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → ((x  : LeftLoopLTerm )  → (P x ))))))
  inductionB p popl pel plinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl pel plinvl x1 ) (inductionB p popl pel plinvl x2 ) )
  
  inductionB p popl pel plinvl eL  = pel 
  
  inductionB p popl pel plinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl pel plinvl x1 ) (inductionB p popl pel plinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftLoopClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → (((x1 x2  : (ClLeftLoopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → ((x  : (ClLeftLoopClTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl pecl plinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl plinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl plinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl x2 ) )
  
  inductionCl _ p psing popcl pecl plinvcl eCl  = pecl 
  
  inductionCl _ p psing popcl pecl plinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl pecl plinvcl x1 ) (inductionCl _ p psing popcl pecl plinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftLoopOLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → (((x1 x2  : (OpLeftLoopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → ((x  : (OpLeftLoopOLTerm n ))  → (P x )))))))
  inductionOp _ p pv popol peol plinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol plinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol plinvol x1 ) (inductionOp _ p pv popol peol plinvol x2 ) )
  
  inductionOp _ p pv popol peol plinvol eOL  = peol 
  
  inductionOp _ p pv popol peol plinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol peol plinvol x1 ) (inductionOp _ p pv popol peol plinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftLoopOL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → (((x1 x2  : (OpLeftLoopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → ((x  : (OpLeftLoopOL2Term2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 plinvol2 x2 ) )
  
  opL' : (  (LeftLoopLTerm   → (LeftLoopLTerm   → LeftLoopLTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  LeftLoopLTerm  )
  eL'  = eL 
  
  linvL' : (  (LeftLoopLTerm   → (LeftLoopLTerm   → LeftLoopLTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  stageB : (LeftLoopLTerm  → (Staged LeftLoopLTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClLeftLoopClTerm A )  → ((ClLeftLoopClTerm A )  → (ClLeftLoopClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClLeftLoopClTerm A ) )
  eCl'  = eCl 
  
  linvCl' : ({A  : Set }  → ((ClLeftLoopClTerm A )  → ((ClLeftLoopClTerm A )  → (ClLeftLoopClTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftLoopClTerm A ) → (Staged (ClLeftLoopClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpLeftLoopOLTerm n )  → ((OpLeftLoopOLTerm n )  → (OpLeftLoopOLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpLeftLoopOLTerm n ) )
  eOL'  = eOL 
  
  linvOL' : ({n  : Nat}  → ((OpLeftLoopOLTerm n )  → ((OpLeftLoopOLTerm n )  → (OpLeftLoopOLTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftLoopOLTerm n ) → (Staged (OpLeftLoopOLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftLoopOL2Term2 n A )  → ((OpLeftLoopOL2Term2 n A )  → (OpLeftLoopOL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpLeftLoopOL2Term2 n A ) )
  eOL2'  = eOL2 
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftLoopOL2Term2 n A )  → ((OpLeftLoopOL2Term2 n A )  → (OpLeftLoopOL2Term2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftLoopOL2Term2 n A ) → (Staged (OpLeftLoopOL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (linvOL2 x1 x2 )  = (stage2 linvOL2' (codeLift2 linvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 
      linvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))