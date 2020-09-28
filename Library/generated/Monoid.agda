module Monoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Monoid (A  : Set )  : Set where
    constructor MonoidC
    field
      op : (A  → (A  → A ))
      e : A 
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
  open Monoid
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP )
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
  record Hom (A1 A2  : Set ) (Mo1  : (Monoid A1 )) (Mo2  : (Monoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mo1 ) x1 x2 ) ) ≡ ((op Mo2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Mo1 )  ) ≡ (e Mo2 ) )
  record RelInterp (A1 A2  : Set ) (Mo1  : (Monoid A1 )) (Mo2  : (Monoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mo1 ) x1 x2 ) ((op Mo2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Mo1 )  (e Mo2 )  ))
  data MonoidTerm  : Set where
    opL : (MonoidTerm   → (MonoidTerm   → MonoidTerm  ))
    eL : MonoidTerm  
  data ClMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClMonoidTerm A ) )
    opCl : ((ClMonoidTerm A )  → ((ClMonoidTerm A )  → (ClMonoidTerm A ) ))
    eCl : (ClMonoidTerm A ) 
  data OpMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMonoidTerm n ) )
    opOL : ((OpMonoidTerm n )  → ((OpMonoidTerm n )  → (OpMonoidTerm n ) ))
    eOL : (OpMonoidTerm n ) 
  data OpMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMonoidTerm2 n A ) )
    sing2 : (A  → (OpMonoidTerm2 n A ) )
    opOL2 : ((OpMonoidTerm2 n A )  → ((OpMonoidTerm2 n A )  → (OpMonoidTerm2 n A ) ))
    eOL2 : (OpMonoidTerm2 n A ) 
  evalB : ({A  : Set }  → ((Monoid A ) → (MonoidTerm  → A )))
  evalB Mo (opL x1 x2 )  = ((op Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalB Mo eL  = (e Mo ) 
  
  evalCl : ({A  : Set }  → ((Monoid A ) → ((ClMonoidTerm A ) → A )))
  evalCl Mo (sing x1 )  = x1 
  
  evalCl Mo (opCl x1 x2 )  = ((op Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalCl Mo eCl  = (e Mo ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Monoid A ) → ((Vec A n ) → ((OpMonoidTerm n ) → A ))))
  evalOp n Mo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mo vars (opOL x1 x2 )  = ((op Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOp n Mo vars eOL  = (e Mo ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Monoid A ) → ((Vec A n ) → ((OpMonoidTerm2 n A ) → A ))))
  evalOpE n Mo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mo vars (sing2 x1 )  = x1 
  
  evalOpE n Mo vars (opOL2 x1 x2 )  = ((op Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  evalOpE n Mo vars eOL2  = (e Mo ) 
  
  inductionB : ((P  : (MonoidTerm  → Set ))  → (((x1 x2  : MonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : MonoidTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (MonoidTerm   → (MonoidTerm   → MonoidTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  MonoidTerm  )
  eL'  = eL 
  
  stageB : (MonoidTerm  → (Staged MonoidTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClMonoidTerm A )  → ((ClMonoidTerm A )  → (ClMonoidTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClMonoidTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClMonoidTerm A ) → (Staged (ClMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpMonoidTerm n )  → ((OpMonoidTerm n )  → (OpMonoidTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpMonoidTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpMonoidTerm n ) → (Staged (OpMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMonoidTerm2 n A )  → ((OpMonoidTerm2 n A )  → (OpMonoidTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpMonoidTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMonoidTerm2 n A ) → (Staged (OpMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 