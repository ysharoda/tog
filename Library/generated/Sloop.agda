module Sloop  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Sloop (A  : Set )  : Set where
    constructor SloopC
    field
      e : A 
      op : (A  → (A  → A ))
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x ))
      antiAbsorbent : ({x y  : A }  → (op x (op x y ) ) ≡ y )
      unipotence : ({x  : A }  → (op x x ) ≡ e )
  open Sloop
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
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP ))
      antiAbsorbentP : ({xP yP  : (Prod AP AP )}  → (opP xP (opP xP yP ) ) ≡ yP )
      unipotenceP : ({xP  : (Prod AP AP )}  → (opP xP xP ) ≡ eP )
  record Hom (A1 A2  : Set ) (Sl1  : (Sloop A1 )) (Sl2  : (Sloop A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-e : (  (hom (e Sl1 )  ) ≡ (e Sl2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Sl1 ) x1 x2 ) ) ≡ ((op Sl2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Sl1  : (Sloop A1 )) (Sl2  : (Sloop A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-e : (  (interp (e Sl1 )  (e Sl2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Sl1 ) x1 x2 ) ((op Sl2 ) y1 y2 ) ))))
  data SloopLTerm  : Set where
    eL : SloopLTerm  
    opL : (SloopLTerm   → (SloopLTerm   → SloopLTerm  ))
  data ClSloopClTerm (A  : Set )  : Set where
    sing : (A  → (ClSloopClTerm A ) )
    eCl : (ClSloopClTerm A ) 
    opCl : ((ClSloopClTerm A )  → ((ClSloopClTerm A )  → (ClSloopClTerm A ) ))
  data OpSloopOLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpSloopOLTerm n ) )
    eOL : (OpSloopOLTerm n ) 
    opOL : ((OpSloopOLTerm n )  → ((OpSloopOLTerm n )  → (OpSloopOLTerm n ) ))
  data OpSloopOL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpSloopOL2Term2 n A ) )
    sing2 : (A  → (OpSloopOL2Term2 n A ) )
    eOL2 : (OpSloopOL2Term2 n A ) 
    opOL2 : ((OpSloopOL2Term2 n A )  → ((OpSloopOL2Term2 n A )  → (OpSloopOL2Term2 n A ) ))
  evalB : ({A  : Set }  → ((Sloop A ) → (SloopLTerm  → A )))
  evalB Sl eL  = (e Sl ) 
  
  evalB Sl (opL x1 x2 )  = ((op Sl ) (evalB Sl x1 ) (evalB Sl x2 ) )
  
  evalCl : ({A  : Set }  → ((Sloop A ) → ((ClSloopClTerm A ) → A )))
  evalCl Sl (sing x1 )  = x1 
  
  evalCl Sl eCl  = (e Sl ) 
  
  evalCl Sl (opCl x1 x2 )  = ((op Sl ) (evalCl Sl x1 ) (evalCl Sl x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Sloop A ) → ((Vec A n ) → ((OpSloopOLTerm n ) → A ))))
  evalOp n Sl vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Sl vars eOL  = (e Sl ) 
  
  evalOp n Sl vars (opOL x1 x2 )  = ((op Sl ) (evalOp n Sl vars x1 ) (evalOp n Sl vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Sloop A ) → ((Vec A n ) → ((OpSloopOL2Term2 n A ) → A ))))
  evalOpE n Sl vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Sl vars (sing2 x1 )  = x1 
  
  evalOpE n Sl vars eOL2  = (e Sl ) 
  
  evalOpE n Sl vars (opOL2 x1 x2 )  = ((op Sl ) (evalOpE n Sl vars x1 ) (evalOpE n Sl vars x2 ) )
  
  inductionB : ((P  : (SloopLTerm  → Set ))  → ((P eL ) → (((x1 x2  : SloopLTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : SloopLTerm )  → (P x )))))
  inductionB p pel popl eL  = pel 
  
  inductionB p pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pel popl x1 ) (inductionB p pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClSloopClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P eCl ) → (((x1 x2  : (ClSloopClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClSloopClTerm A ))  → (P x ))))))
  inductionCl _ p psing pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pecl popcl x1 ) (inductionCl _ p psing pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpSloopOLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P eOL ) → (((x1 x2  : (OpSloopOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpSloopOLTerm n ))  → (P x ))))))
  inductionOp _ p pv peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv peol popol eOL  = peol 
  
  inductionOp _ p pv peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv peol popol x1 ) (inductionOp _ p pv peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpSloopOL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P eOL2 ) → (((x1 x2  : (OpSloopOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpSloopOL2Term2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 peol2 popol2 x2 ) )
  
  eL' : (  SloopLTerm  )
  eL'  = eL 
  
  opL' : (  (SloopLTerm   → (SloopLTerm   → SloopLTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (SloopLTerm  → (Staged SloopLTerm  ))
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  eCl' : ({A  : Set }  → (ClSloopClTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClSloopClTerm A )  → ((ClSloopClTerm A )  → (ClSloopClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClSloopClTerm A ) → (Staged (ClSloopClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  eOL' : ({n  : Nat}  → (OpSloopOLTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpSloopOLTerm n )  → ((OpSloopOLTerm n )  → (OpSloopOLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpSloopOLTerm n ) → (Staged (OpSloopOLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpSloopOL2Term2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpSloopOL2Term2 n A )  → ((OpSloopOL2Term2 n A )  → (OpSloopOL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpSloopOL2Term2 n A ) → (Staged (OpSloopOL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))