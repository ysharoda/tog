
 module IdempotentMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IdempotentMagma (A  : Set )  : Set where
    constructor IdempotentMagmaC
    field
      op : (A  → (A  → A ))
      idempotent_op : ({x  : A }  → (op x x ) ≡ x ) 
  
  open IdempotentMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      idempotent_opP : ({xP  : (Prod AP AP )}  → (opP xP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Id1  : (IdempotentMagma A1 )) (Id2  : (IdempotentMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Id1 ) x1 x2 ) ) ≡ ((op Id2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Id1  : (IdempotentMagma A1 )) (Id2  : (IdempotentMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Id1 ) x1 x2 ) ((op Id2 ) y1 y2 ) )))) 
  
  data IdempotentMagmaTerm  : Set where
    opL : (IdempotentMagmaTerm   → (IdempotentMagmaTerm   → IdempotentMagmaTerm  )) 
  
  data ClIdempotentMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClIdempotentMagmaTerm A ) )
    opCl : ((ClIdempotentMagmaTerm A )  → ((ClIdempotentMagmaTerm A )  → (ClIdempotentMagmaTerm A ) )) 
  
  data OpIdempotentMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpIdempotentMagmaTerm n ) )
    opOL : ((OpIdempotentMagmaTerm n )  → ((OpIdempotentMagmaTerm n )  → (OpIdempotentMagmaTerm n ) )) 
  
  data OpIdempotentMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpIdempotentMagmaTerm2 n A ) )
    sing2 : (A  → (OpIdempotentMagmaTerm2 n A ) )
    opOL2 : ((OpIdempotentMagmaTerm2 n A )  → ((OpIdempotentMagmaTerm2 n A )  → (OpIdempotentMagmaTerm2 n A ) )) 
  
  simplifyB : (IdempotentMagmaTerm  → IdempotentMagmaTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClIdempotentMagmaTerm A ) → (ClIdempotentMagmaTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpIdempotentMagmaTerm n ) → (OpIdempotentMagmaTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentMagmaTerm2 n A ) → (OpIdempotentMagmaTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((IdempotentMagma A ) → (IdempotentMagmaTerm  → A )))
  evalB Id (opL x1 x2 )  = ((op Id ) (evalB Id x1 ) (evalB Id x2 ) )
  
  evalCl : ({A  : Set }  → ((IdempotentMagma A ) → ((ClIdempotentMagmaTerm A ) → A )))
  evalCl Id (sing x1 )  = x1 
  
  evalCl Id (opCl x1 x2 )  = ((op Id ) (evalCl Id x1 ) (evalCl Id x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((IdempotentMagma A ) → ((Vec A n ) → ((OpIdempotentMagmaTerm n ) → A ))))
  evalOp n Id vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Id vars (opOL x1 x2 )  = ((op Id ) (evalOp n Id vars x1 ) (evalOp n Id vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((IdempotentMagma A ) → ((Vec A n ) → ((OpIdempotentMagmaTerm2 n A ) → A ))))
  evalOpE n Id vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Id vars (sing2 x1 )  = x1 
  
  evalOpE n Id vars (opOL2 x1 x2 )  = ((op Id ) (evalOpE n Id vars x1 ) (evalOpE n Id vars x2 ) )
  
  inductionB : ((P  : (IdempotentMagmaTerm  → Set ))  → (((x1 x2  : IdempotentMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : IdempotentMagmaTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClIdempotentMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClIdempotentMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClIdempotentMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpIdempotentMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpIdempotentMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpIdempotentMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpIdempotentMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpIdempotentMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpIdempotentMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (IdempotentMagmaTerm   → (IdempotentMagmaTerm   → IdempotentMagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (IdempotentMagmaTerm  → (Staged IdempotentMagmaTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClIdempotentMagmaTerm A )  → ((ClIdempotentMagmaTerm A )  → (ClIdempotentMagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClIdempotentMagmaTerm A ) → (Staged (ClIdempotentMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpIdempotentMagmaTerm n )  → ((OpIdempotentMagmaTerm n )  → (OpIdempotentMagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpIdempotentMagmaTerm n ) → (Staged (OpIdempotentMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpIdempotentMagmaTerm2 n A )  → ((OpIdempotentMagmaTerm2 n A )  → (OpIdempotentMagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentMagmaTerm2 n A ) → (Staged (OpIdempotentMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
