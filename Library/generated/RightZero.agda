module RightZero  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightZero (A  : Set )  : Set where
    constructor RightZeroC
    field
      e : A 
      op : (A  → (A  → A ))
      rightZero_op_e : ({x  : A }  → (op x e ) ≡ e )
  open RightZero
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      eS : AS 
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      eP : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      rightZero_op_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ eP )
  record Hom (A1 A2  : Set ) (Ri1  : (RightZero A1 )) (Ri2  : (RightZero A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-e : (  (hom (e Ri1 )  ) ≡ (e Ri2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightZero A1 )) (Ri2  : (RightZero A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-e : (  (interp (e Ri1 )  (e Ri2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) ))))
  data RightZeroTerm  : Set where
    eL : RightZeroTerm  
    opL : (RightZeroTerm   → (RightZeroTerm   → RightZeroTerm  ))
  data ClRightZeroTerm (A  : Set )  : Set where
    sing : (A  → (ClRightZeroTerm A ) )
    eCl : (ClRightZeroTerm A ) 
    opCl : ((ClRightZeroTerm A )  → ((ClRightZeroTerm A )  → (ClRightZeroTerm A ) ))
  data OpRightZeroTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightZeroTerm n ) )
    eOL : (OpRightZeroTerm n ) 
    opOL : ((OpRightZeroTerm n )  → ((OpRightZeroTerm n )  → (OpRightZeroTerm n ) ))
  data OpRightZeroTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightZeroTerm2 n A ) )
    sing2 : (A  → (OpRightZeroTerm2 n A ) )
    eOL2 : (OpRightZeroTerm2 n A ) 
    opOL2 : ((OpRightZeroTerm2 n A )  → ((OpRightZeroTerm2 n A )  → (OpRightZeroTerm2 n A ) ))
  evalB : ({A  : Set }  → ((RightZero A ) → (RightZeroTerm  → A )))
  evalB Ri eL  = (e Ri ) 
  
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightZero A ) → ((ClRightZeroTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri eCl  = (e Ri ) 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightZero A ) → ((Vec A n ) → ((OpRightZeroTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars eOL  = (e Ri ) 
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightZero A ) → ((Vec A n ) → ((OpRightZeroTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars eOL2  = (e Ri ) 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightZeroTerm  → Set ))  → ((P eL ) → (((x1 x2  : RightZeroTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : RightZeroTerm )  → (P x )))))
  inductionB p pel popl eL  = pel 
  
  inductionB p pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pel popl x1 ) (inductionB p pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightZeroTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P eCl ) → (((x1 x2  : (ClRightZeroTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClRightZeroTerm A ))  → (P x ))))))
  inductionCl _ p psing pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pecl popcl x1 ) (inductionCl _ p psing pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightZeroTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P eOL ) → (((x1 x2  : (OpRightZeroTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpRightZeroTerm n ))  → (P x ))))))
  inductionOp _ p pv peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv peol popol eOL  = peol 
  
  inductionOp _ p pv peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv peol popol x1 ) (inductionOp _ p pv peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightZeroTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P eOL2 ) → (((x1 x2  : (OpRightZeroTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpRightZeroTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 peol2 popol2 x2 ) )
  
  eL' : (  RightZeroTerm  )
  eL'  = eL 
  
  opL' : (  (RightZeroTerm   → (RightZeroTerm   → RightZeroTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (RightZeroTerm  → (Staged RightZeroTerm  ))
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  eCl' : ({A  : Set }  → (ClRightZeroTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClRightZeroTerm A )  → ((ClRightZeroTerm A )  → (ClRightZeroTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightZeroTerm A ) → (Staged (ClRightZeroTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  eOL' : ({n  : Nat}  → (OpRightZeroTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpRightZeroTerm n )  → ((OpRightZeroTerm n )  → (OpRightZeroTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightZeroTerm n ) → (Staged (OpRightZeroTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpRightZeroTerm2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightZeroTerm2 n A )  → ((OpRightZeroTerm2 n A )  → (OpRightZeroTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightZeroTerm2 n A ) → (Staged (OpRightZeroTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))