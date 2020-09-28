module LeftQuasiGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftQuasiGroup (A  : Set )  : Set where
    constructor LeftQuasiGroupC
    field
      op : (A  → (A  → A ))
      linv : (A  → (A  → A ))
      leftCancel : ({x y  : A }  → (op x (linv x y ) ) ≡ y )
      lefCancelOp : ({x y  : A }  → (linv x (op x y ) ) ≡ y )
  open LeftQuasiGroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      linvS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      linvP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftCancelP : ({xP yP  : (Prod AP AP )}  → (opP xP (linvP xP yP ) ) ≡ yP )
      lefCancelOpP : ({xP yP  : (Prod AP AP )}  → (linvP xP (opP xP yP ) ) ≡ yP )
  record Hom (A1 A2  : Set ) (Le1  : (LeftQuasiGroup A1 )) (Le2  : (LeftQuasiGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Le1 ) x1 x2 ) ) ≡ ((op Le2 ) (hom x1 ) (hom x2 ) ))
      pres-linv : ({x1  : A1} {x2  : A1}  → (hom ((linv Le1 ) x1 x2 ) ) ≡ ((linv Le2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftQuasiGroup A1 )) (Le2  : (LeftQuasiGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Le1 ) x1 x2 ) ((op Le2 ) y1 y2 ) ))))
      interp-linv : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((linv Le1 ) x1 x2 ) ((linv Le2 ) y1 y2 ) ))))
  data LeftQuasiGroupTerm  : Set where
    opL : (LeftQuasiGroupTerm   → (LeftQuasiGroupTerm   → LeftQuasiGroupTerm  ))
    linvL : (LeftQuasiGroupTerm   → (LeftQuasiGroupTerm   → LeftQuasiGroupTerm  ))
  data ClLeftQuasiGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftQuasiGroupTerm A ) )
    opCl : ((ClLeftQuasiGroupTerm A )  → ((ClLeftQuasiGroupTerm A )  → (ClLeftQuasiGroupTerm A ) ))
    linvCl : ((ClLeftQuasiGroupTerm A )  → ((ClLeftQuasiGroupTerm A )  → (ClLeftQuasiGroupTerm A ) ))
  data OpLeftQuasiGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftQuasiGroupTerm n ) )
    opOL : ((OpLeftQuasiGroupTerm n )  → ((OpLeftQuasiGroupTerm n )  → (OpLeftQuasiGroupTerm n ) ))
    linvOL : ((OpLeftQuasiGroupTerm n )  → ((OpLeftQuasiGroupTerm n )  → (OpLeftQuasiGroupTerm n ) ))
  data OpLeftQuasiGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftQuasiGroupTerm2 n A ) )
    sing2 : (A  → (OpLeftQuasiGroupTerm2 n A ) )
    opOL2 : ((OpLeftQuasiGroupTerm2 n A )  → ((OpLeftQuasiGroupTerm2 n A )  → (OpLeftQuasiGroupTerm2 n A ) ))
    linvOL2 : ((OpLeftQuasiGroupTerm2 n A )  → ((OpLeftQuasiGroupTerm2 n A )  → (OpLeftQuasiGroupTerm2 n A ) ))
  evalB : ({A  : Set }  → ((LeftQuasiGroup A ) → (LeftQuasiGroupTerm  → A )))
  evalB Le (opL x1 x2 )  = ((op Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalB Le (linvL x1 x2 )  = ((linv Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftQuasiGroup A ) → ((ClLeftQuasiGroupTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (opCl x1 x2 )  = ((op Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalCl Le (linvCl x1 x2 )  = ((linv Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftQuasiGroup A ) → ((Vec A n ) → ((OpLeftQuasiGroupTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (opOL x1 x2 )  = ((op Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOp n Le vars (linvOL x1 x2 )  = ((linv Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftQuasiGroup A ) → ((Vec A n ) → ((OpLeftQuasiGroupTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (opOL2 x1 x2 )  = ((op Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  evalOpE n Le vars (linvOL2 x1 x2 )  = ((linv Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftQuasiGroupTerm  → Set ))  → (((x1 x2  : LeftQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1 x2  : LeftQuasiGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (linvL x1 x2 ) )))) → ((x  : LeftQuasiGroupTerm )  → (P x )))))
  inductionB p popl plinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl plinvl x1 ) (inductionB p popl plinvl x2 ) )
  
  inductionB p popl plinvl (linvL x1 x2 )  = (plinvl _ _ (inductionB p popl plinvl x1 ) (inductionB p popl plinvl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftQuasiGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1 x2  : (ClLeftQuasiGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (linvCl x1 x2 ) )))) → ((x  : (ClLeftQuasiGroupTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl plinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl plinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl plinvcl x1 ) (inductionCl _ p psing popcl plinvcl x2 ) )
  
  inductionCl _ p psing popcl plinvcl (linvCl x1 x2 )  = (plinvcl _ _ (inductionCl _ p psing popcl plinvcl x1 ) (inductionCl _ p psing popcl plinvcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftQuasiGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1 x2  : (OpLeftQuasiGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL x1 x2 ) )))) → ((x  : (OpLeftQuasiGroupTerm n ))  → (P x ))))))
  inductionOp _ p pv popol plinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol plinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol plinvol x1 ) (inductionOp _ p pv popol plinvol x2 ) )
  
  inductionOp _ p pv popol plinvol (linvOL x1 x2 )  = (plinvol _ _ (inductionOp _ p pv popol plinvol x1 ) (inductionOp _ p pv popol plinvol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftQuasiGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1 x2  : (OpLeftQuasiGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (linvOL2 x1 x2 ) )))) → ((x  : (OpLeftQuasiGroupTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 plinvol2 (linvOL2 x1 x2 )  = (plinvol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 plinvol2 x2 ) )
  
  opL' : (  (LeftQuasiGroupTerm   → (LeftQuasiGroupTerm   → LeftQuasiGroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  linvL' : (  (LeftQuasiGroupTerm   → (LeftQuasiGroupTerm   → LeftQuasiGroupTerm  )))
  linvL' x1 x2  = (linvL x1 x2 )
  
  stageB : (LeftQuasiGroupTerm  → (Staged LeftQuasiGroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (linvL x1 x2 )  = (stage2 linvL' (codeLift2 linvL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClLeftQuasiGroupTerm A )  → ((ClLeftQuasiGroupTerm A )  → (ClLeftQuasiGroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  linvCl' : ({A  : Set }  → ((ClLeftQuasiGroupTerm A )  → ((ClLeftQuasiGroupTerm A )  → (ClLeftQuasiGroupTerm A ) )))
  linvCl' x1 x2  = (linvCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftQuasiGroupTerm A ) → (Staged (ClLeftQuasiGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (linvCl x1 x2 )  = (stage2 linvCl' (codeLift2 linvCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpLeftQuasiGroupTerm n )  → ((OpLeftQuasiGroupTerm n )  → (OpLeftQuasiGroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  linvOL' : ({n  : Nat}  → ((OpLeftQuasiGroupTerm n )  → ((OpLeftQuasiGroupTerm n )  → (OpLeftQuasiGroupTerm n ) )))
  linvOL' x1 x2  = (linvOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftQuasiGroupTerm n ) → (Staged (OpLeftQuasiGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (linvOL x1 x2 )  = (stage2 linvOL' (codeLift2 linvOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftQuasiGroupTerm2 n A )  → ((OpLeftQuasiGroupTerm2 n A )  → (OpLeftQuasiGroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  linvOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftQuasiGroupTerm2 n A )  → ((OpLeftQuasiGroupTerm2 n A )  → (OpLeftQuasiGroupTerm2 n A ) )))
  linvOL2' x1 x2  = (linvOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftQuasiGroupTerm2 n A ) → (Staged (OpLeftQuasiGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (linvOL2 x1 x2 )  = (stage2 linvOL2' (codeLift2 linvOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      linvT : ((Repr A )  → ((Repr A )  → (Repr A ) ))