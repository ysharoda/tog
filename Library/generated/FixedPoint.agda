module FixedPoint  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record FixedPoint (A  : Set )  : Set where
    constructor FixedPointC
    field
      prim : (A  → A )
      e : A 
      fixes_prim_e : (prim e ) ≡ e 
  open FixedPoint
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      eS : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      eP : (Prod AP AP )
      fixes_prim_eP : (primP eP ) ≡ eP 
  record Hom (A1 A2  : Set ) (Fi1  : (FixedPoint A1 )) (Fi2  : (FixedPoint A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Fi1 ) x1 ) ) ≡ ((prim Fi2 ) (hom x1 ) ))
      pres-e : (  (hom (e Fi1 )  ) ≡ (e Fi2 ) )
  record RelInterp (A1 A2  : Set ) (Fi1  : (FixedPoint A1 )) (Fi2  : (FixedPoint A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Fi1 ) x1 ) ((prim Fi2 ) y1 ) )))
      interp-e : (  (interp (e Fi1 )  (e Fi2 )  ))
  data FixedPointTerm  : Set where
    primL : (FixedPointTerm   → FixedPointTerm  )
    eL : FixedPointTerm  
  data ClFixedPointTerm (A  : Set )  : Set where
    sing : (A  → (ClFixedPointTerm A ) )
    primCl : ((ClFixedPointTerm A )  → (ClFixedPointTerm A ) )
    eCl : (ClFixedPointTerm A ) 
  data OpFixedPointTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpFixedPointTerm n ) )
    primOL : ((OpFixedPointTerm n )  → (OpFixedPointTerm n ) )
    eOL : (OpFixedPointTerm n ) 
  data OpFixedPointTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpFixedPointTerm2 n A ) )
    sing2 : (A  → (OpFixedPointTerm2 n A ) )
    primOL2 : ((OpFixedPointTerm2 n A )  → (OpFixedPointTerm2 n A ) )
    eOL2 : (OpFixedPointTerm2 n A ) 
  evalB : ({A  : Set }  → ((FixedPoint A ) → (FixedPointTerm  → A )))
  evalB Fi (primL x1 )  = ((prim Fi ) (evalB Fi x1 ) )
  
  evalB Fi eL  = (e Fi ) 
  
  evalCl : ({A  : Set }  → ((FixedPoint A ) → ((ClFixedPointTerm A ) → A )))
  evalCl Fi (sing x1 )  = x1 
  
  evalCl Fi (primCl x1 )  = ((prim Fi ) (evalCl Fi x1 ) )
  
  evalCl Fi eCl  = (e Fi ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((FixedPoint A ) → ((Vec A n ) → ((OpFixedPointTerm n ) → A ))))
  evalOp n Fi vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Fi vars (primOL x1 )  = ((prim Fi ) (evalOp n Fi vars x1 ) )
  
  evalOp n Fi vars eOL  = (e Fi ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((FixedPoint A ) → ((Vec A n ) → ((OpFixedPointTerm2 n A ) → A ))))
  evalOpE n Fi vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Fi vars (sing2 x1 )  = x1 
  
  evalOpE n Fi vars (primOL2 x1 )  = ((prim Fi ) (evalOpE n Fi vars x1 ) )
  
  evalOpE n Fi vars eOL2  = (e Fi ) 
  
  inductionB : ((P  : (FixedPointTerm  → Set ))  → (((x1  : FixedPointTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((P eL ) → ((x  : FixedPointTerm )  → (P x )))))
  inductionB p ppriml pel (primL x1 )  = (ppriml _ (inductionB p ppriml pel x1 ) )
  
  inductionB p ppriml pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClFixedPointTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClFixedPointTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((P eCl ) → ((x  : (ClFixedPointTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl pecl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl pecl x1 ) )
  
  inductionCl _ p psing pprimcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpFixedPointTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpFixedPointTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((P eOL ) → ((x  : (OpFixedPointTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol peol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol peol x1 ) )
  
  inductionOp _ p pv pprimol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpFixedPointTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpFixedPointTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((P eOL2 ) → ((x  : (OpFixedPointTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 peol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 peol2 eOL2  = peol2 
  
  primL' : (  (FixedPointTerm   → FixedPointTerm  ))
  primL' x1  = (primL x1 )
  
  eL' : (  FixedPointTerm  )
  eL'  = eL 
  
  stageB : (FixedPointTerm  → (Staged FixedPointTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB eL  = (Now eL )
  
  primCl' : ({A  : Set }  → ((ClFixedPointTerm A )  → (ClFixedPointTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  eCl' : ({A  : Set }  → (ClFixedPointTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClFixedPointTerm A ) → (Staged (ClFixedPointTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  primOL' : ({n  : Nat}  → ((OpFixedPointTerm n )  → (OpFixedPointTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  eOL' : ({n  : Nat}  → (OpFixedPointTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpFixedPointTerm n ) → (Staged (OpFixedPointTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpFixedPointTerm2 n A )  → (OpFixedPointTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpFixedPointTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpFixedPointTerm2 n A ) → (Staged (OpFixedPointTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      eT : (Repr A ) 