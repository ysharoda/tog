module LeftMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftMonoid (A  : Set )  : Set where
    constructor LeftMonoidC
    field
      op : (A  → (A  → A ))
      e : A 
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
  open LeftMonoid
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
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
  record Hom (A1 A2  : Set ) (Le1  : (LeftMonoid A1 )) (Le2  : (LeftMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Le1 ) x1 x2 ) ) ≡ ((op Le2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Le1 )  ) ≡ (e Le2 ) )
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftMonoid A1 )) (Le2  : (LeftMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Le1 ) x1 x2 ) ((op Le2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Le1 )  (e Le2 )  ))
  data LeftMonoidTerm  : Set where
    opL : (LeftMonoidTerm   → (LeftMonoidTerm   → LeftMonoidTerm  ))
    eL : LeftMonoidTerm  
  data ClLeftMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftMonoidTerm A ) )
    opCl : ((ClLeftMonoidTerm A )  → ((ClLeftMonoidTerm A )  → (ClLeftMonoidTerm A ) ))
    eCl : (ClLeftMonoidTerm A ) 
  data OpLeftMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftMonoidTerm n ) )
    opOL : ((OpLeftMonoidTerm n )  → ((OpLeftMonoidTerm n )  → (OpLeftMonoidTerm n ) ))
    eOL : (OpLeftMonoidTerm n ) 
  data OpLeftMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftMonoidTerm2 n A ) )
    sing2 : (A  → (OpLeftMonoidTerm2 n A ) )
    opOL2 : ((OpLeftMonoidTerm2 n A )  → ((OpLeftMonoidTerm2 n A )  → (OpLeftMonoidTerm2 n A ) ))
    eOL2 : (OpLeftMonoidTerm2 n A ) 
  evalB : ({A  : Set }  → ((LeftMonoid A ) → (LeftMonoidTerm  → A )))
  evalB Le (opL x1 x2 )  = ((op Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalB Le eL  = (e Le ) 
  
  evalCl : ({A  : Set }  → ((LeftMonoid A ) → ((ClLeftMonoidTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (opCl x1 x2 )  = ((op Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalCl Le eCl  = (e Le ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftMonoid A ) → ((Vec A n ) → ((OpLeftMonoidTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (opOL x1 x2 )  = ((op Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOp n Le vars eOL  = (e Le ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftMonoid A ) → ((Vec A n ) → ((OpLeftMonoidTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (opOL2 x1 x2 )  = ((op Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  evalOpE n Le vars eOL2  = (e Le ) 
  
  inductionB : ((P  : (LeftMonoidTerm  → Set ))  → (((x1 x2  : LeftMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : LeftMonoidTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClLeftMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpLeftMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpLeftMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (LeftMonoidTerm   → (LeftMonoidTerm   → LeftMonoidTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  LeftMonoidTerm  )
  eL'  = eL 
  
  stageB : (LeftMonoidTerm  → (Staged LeftMonoidTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClLeftMonoidTerm A )  → ((ClLeftMonoidTerm A )  → (ClLeftMonoidTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClLeftMonoidTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClLeftMonoidTerm A ) → (Staged (ClLeftMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpLeftMonoidTerm n )  → ((OpLeftMonoidTerm n )  → (OpLeftMonoidTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpLeftMonoidTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpLeftMonoidTerm n ) → (Staged (OpLeftMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftMonoidTerm2 n A )  → ((OpLeftMonoidTerm2 n A )  → (OpLeftMonoidTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpLeftMonoidTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftMonoidTerm2 n A ) → (Staged (OpLeftMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 