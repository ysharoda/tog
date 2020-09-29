
 module IdempotentUnary  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IdempotentUnary (A  : Set )  : Set where
    constructor IdempotentUnaryC
    field
      prim : (A  → A )
      idempotent_prim : ({x  : A }  → (prim (prim x ) ) ≡ (prim x )) 
  
  open IdempotentUnary
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      idempotent_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ (primP xP )) 
  
  record Hom (A1 A2  : Set ) (Id1  : (IdempotentUnary A1 )) (Id2  : (IdempotentUnary A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Id1 ) x1 ) ) ≡ ((prim Id2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Id1  : (IdempotentUnary A1 )) (Id2  : (IdempotentUnary A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Id1 ) x1 ) ((prim Id2 ) y1 ) ))) 
  
  data IdempotentUnaryTerm  : Set where
    primL : (IdempotentUnaryTerm   → IdempotentUnaryTerm  ) 
  
  data ClIdempotentUnaryTerm (A  : Set )  : Set where
    sing : (A  → (ClIdempotentUnaryTerm A ) )
    primCl : ((ClIdempotentUnaryTerm A )  → (ClIdempotentUnaryTerm A ) ) 
  
  data OpIdempotentUnaryTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpIdempotentUnaryTerm n ) )
    primOL : ((OpIdempotentUnaryTerm n )  → (OpIdempotentUnaryTerm n ) ) 
  
  data OpIdempotentUnaryTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpIdempotentUnaryTerm2 n A ) )
    sing2 : (A  → (OpIdempotentUnaryTerm2 n A ) )
    primOL2 : ((OpIdempotentUnaryTerm2 n A )  → (OpIdempotentUnaryTerm2 n A ) ) 
  
  simplifyB : (IdempotentUnaryTerm  → IdempotentUnaryTerm )
  simplifyB (primL (primL x ) )  = (primL x )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClIdempotentUnaryTerm A ) → (ClIdempotentUnaryTerm A )))
  simplifyCl _ (primCl (primCl x ) )  = (primCl x )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpIdempotentUnaryTerm n ) → (OpIdempotentUnaryTerm n )))
  simplifyOp _ (primOL (primOL x ) )  = (primOL x )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentUnaryTerm2 n A ) → (OpIdempotentUnaryTerm2 n A )))
  simplifyOpE _ _ (primOL2 (primOL2 x ) )  = (primOL2 x )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((IdempotentUnary A ) → (IdempotentUnaryTerm  → A )))
  evalB Id (primL x1 )  = ((prim Id ) (evalB Id x1 ) )
  
  evalCl : ({A  : Set }  → ((IdempotentUnary A ) → ((ClIdempotentUnaryTerm A ) → A )))
  evalCl Id (sing x1 )  = x1 
  
  evalCl Id (primCl x1 )  = ((prim Id ) (evalCl Id x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((IdempotentUnary A ) → ((Vec A n ) → ((OpIdempotentUnaryTerm n ) → A ))))
  evalOp n Id vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Id vars (primOL x1 )  = ((prim Id ) (evalOp n Id vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((IdempotentUnary A ) → ((Vec A n ) → ((OpIdempotentUnaryTerm2 n A ) → A ))))
  evalOpE n Id vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Id vars (sing2 x1 )  = x1 
  
  evalOpE n Id vars (primOL2 x1 )  = ((prim Id ) (evalOpE n Id vars x1 ) )
  
  inductionB : ((P  : (IdempotentUnaryTerm  → Set ))  → (((x1  : IdempotentUnaryTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : IdempotentUnaryTerm )  → (P x ))))
  inductionB p ppriml (primL x1 )  = (ppriml _ (inductionB p ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClIdempotentUnaryTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClIdempotentUnaryTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClIdempotentUnaryTerm A ))  → (P x )))))
  inductionCl _ p psing pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpIdempotentUnaryTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpIdempotentUnaryTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpIdempotentUnaryTerm n ))  → (P x )))))
  inductionOp _ p pv pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpIdempotentUnaryTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpIdempotentUnaryTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpIdempotentUnaryTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 x1 ) )
  
  primL' : (  (IdempotentUnaryTerm   → IdempotentUnaryTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (IdempotentUnaryTerm  → (Staged IdempotentUnaryTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  primCl' : ({A  : Set }  → ((ClIdempotentUnaryTerm A )  → (ClIdempotentUnaryTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClIdempotentUnaryTerm A ) → (Staged (ClIdempotentUnaryTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  primOL' : ({n  : Nat}  → ((OpIdempotentUnaryTerm n )  → (OpIdempotentUnaryTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpIdempotentUnaryTerm n ) → (Staged (OpIdempotentUnaryTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpIdempotentUnaryTerm2 n A )  → (OpIdempotentUnaryTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentUnaryTerm2 n A ) → (Staged (OpIdempotentUnaryTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) ) 
   
