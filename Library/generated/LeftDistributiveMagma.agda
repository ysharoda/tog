module LeftDistributiveMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftDistributiveMagma (A  : Set )  : Set where
    constructor LeftDistributiveMagmaC
    field
      op : (A  → (A  → A ))
      leftDistributive : ({x y z  : A }  → (op x (op y z ) ) ≡ (op (op x y ) (op x z ) ))
  open LeftDistributiveMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftDistributiveP : ({xP yP zP  : (Prod AP AP )}  → (opP xP (opP yP zP ) ) ≡ (opP (opP xP yP ) (opP xP zP ) ))
  record Hom (A1 A2  : Set ) (Le1  : (LeftDistributiveMagma A1 )) (Le2  : (LeftDistributiveMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Le1 ) x1 x2 ) ) ≡ ((op Le2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftDistributiveMagma A1 )) (Le2  : (LeftDistributiveMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Le1 ) x1 x2 ) ((op Le2 ) y1 y2 ) ))))
  data LeftDistributiveMagmaTerm  : Set where
    opL : (LeftDistributiveMagmaTerm   → (LeftDistributiveMagmaTerm   → LeftDistributiveMagmaTerm  ))
  data ClLeftDistributiveMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftDistributiveMagmaTerm A ) )
    opCl : ((ClLeftDistributiveMagmaTerm A )  → ((ClLeftDistributiveMagmaTerm A )  → (ClLeftDistributiveMagmaTerm A ) ))
  data OpLeftDistributiveMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftDistributiveMagmaTerm n ) )
    opOL : ((OpLeftDistributiveMagmaTerm n )  → ((OpLeftDistributiveMagmaTerm n )  → (OpLeftDistributiveMagmaTerm n ) ))
  data OpLeftDistributiveMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftDistributiveMagmaTerm2 n A ) )
    sing2 : (A  → (OpLeftDistributiveMagmaTerm2 n A ) )
    opOL2 : ((OpLeftDistributiveMagmaTerm2 n A )  → ((OpLeftDistributiveMagmaTerm2 n A )  → (OpLeftDistributiveMagmaTerm2 n A ) ))
  evalB : ({A  : Set }  → ((LeftDistributiveMagma A ) → (LeftDistributiveMagmaTerm  → A )))
  evalB Le (opL x1 x2 )  = ((op Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftDistributiveMagma A ) → ((ClLeftDistributiveMagmaTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le (opCl x1 x2 )  = ((op Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftDistributiveMagma A ) → ((Vec A n ) → ((OpLeftDistributiveMagmaTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars (opOL x1 x2 )  = ((op Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftDistributiveMagma A ) → ((Vec A n ) → ((OpLeftDistributiveMagmaTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars (opOL2 x1 x2 )  = ((op Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftDistributiveMagmaTerm  → Set ))  → (((x1 x2  : LeftDistributiveMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : LeftDistributiveMagmaTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftDistributiveMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClLeftDistributiveMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClLeftDistributiveMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftDistributiveMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpLeftDistributiveMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpLeftDistributiveMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftDistributiveMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpLeftDistributiveMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpLeftDistributiveMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (LeftDistributiveMagmaTerm   → (LeftDistributiveMagmaTerm   → LeftDistributiveMagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (LeftDistributiveMagmaTerm  → (Staged LeftDistributiveMagmaTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClLeftDistributiveMagmaTerm A )  → ((ClLeftDistributiveMagmaTerm A )  → (ClLeftDistributiveMagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftDistributiveMagmaTerm A ) → (Staged (ClLeftDistributiveMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpLeftDistributiveMagmaTerm n )  → ((OpLeftDistributiveMagmaTerm n )  → (OpLeftDistributiveMagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftDistributiveMagmaTerm n ) → (Staged (OpLeftDistributiveMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftDistributiveMagmaTerm2 n A )  → ((OpLeftDistributiveMagmaTerm2 n A )  → (OpLeftDistributiveMagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftDistributiveMagmaTerm2 n A ) → (Staged (OpLeftDistributiveMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))