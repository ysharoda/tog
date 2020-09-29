
 module BooleanGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record BooleanGroup (A  : Set )  : Set where
    constructor BooleanGroupC
    field
      e : A 
      op : (A  → (A  → A ))
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      unipotence : ({x  : A }  → (op x x ) ≡ e ) 
  
  open BooleanGroup
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
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP )
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      unipotenceP : ({xP  : (Prod AP AP )}  → (opP xP xP ) ≡ eP ) 
  
  record Hom (A1 A2  : Set ) (Bo1  : (BooleanGroup A1 )) (Bo2  : (BooleanGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-e : (  (hom (e Bo1 )  ) ≡ (e Bo2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Bo1 ) x1 x2 ) ) ≡ ((op Bo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Bo1  : (BooleanGroup A1 )) (Bo2  : (BooleanGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-e : (  (interp (e Bo1 )  (e Bo2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Bo1 ) x1 x2 ) ((op Bo2 ) y1 y2 ) )))) 
  
  data BooleanGroupTerm  : Set where
    eL : BooleanGroupTerm  
    opL : (BooleanGroupTerm   → (BooleanGroupTerm   → BooleanGroupTerm  )) 
  
  data ClBooleanGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClBooleanGroupTerm A ) )
    eCl : (ClBooleanGroupTerm A ) 
    opCl : ((ClBooleanGroupTerm A )  → ((ClBooleanGroupTerm A )  → (ClBooleanGroupTerm A ) )) 
  
  data OpBooleanGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpBooleanGroupTerm n ) )
    eOL : (OpBooleanGroupTerm n ) 
    opOL : ((OpBooleanGroupTerm n )  → ((OpBooleanGroupTerm n )  → (OpBooleanGroupTerm n ) )) 
  
  data OpBooleanGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpBooleanGroupTerm2 n A ) )
    sing2 : (A  → (OpBooleanGroupTerm2 n A ) )
    eOL2 : (OpBooleanGroupTerm2 n A ) 
    opOL2 : ((OpBooleanGroupTerm2 n A )  → ((OpBooleanGroupTerm2 n A )  → (OpBooleanGroupTerm2 n A ) )) 
  
  simplifyB : (BooleanGroupTerm  → BooleanGroupTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB (opL x eL )  = x 
  
  simplifyB eL  = eL 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClBooleanGroupTerm A ) → (ClBooleanGroupTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ (opCl x eCl )  = x 
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpBooleanGroupTerm n ) → (OpBooleanGroupTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ (opOL x eOL )  = x 
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpBooleanGroupTerm2 n A ) → (OpBooleanGroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x eOL2 )  = x 
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((BooleanGroup A ) → (BooleanGroupTerm  → A )))
  evalB Bo eL  = (e Bo ) 
  
  evalB Bo (opL x1 x2 )  = ((op Bo ) (evalB Bo x1 ) (evalB Bo x2 ) )
  
  evalCl : ({A  : Set }  → ((BooleanGroup A ) → ((ClBooleanGroupTerm A ) → A )))
  evalCl Bo (sing x1 )  = x1 
  
  evalCl Bo eCl  = (e Bo ) 
  
  evalCl Bo (opCl x1 x2 )  = ((op Bo ) (evalCl Bo x1 ) (evalCl Bo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((BooleanGroup A ) → ((Vec A n ) → ((OpBooleanGroupTerm n ) → A ))))
  evalOp n Bo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Bo vars eOL  = (e Bo ) 
  
  evalOp n Bo vars (opOL x1 x2 )  = ((op Bo ) (evalOp n Bo vars x1 ) (evalOp n Bo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((BooleanGroup A ) → ((Vec A n ) → ((OpBooleanGroupTerm2 n A ) → A ))))
  evalOpE n Bo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Bo vars (sing2 x1 )  = x1 
  
  evalOpE n Bo vars eOL2  = (e Bo ) 
  
  evalOpE n Bo vars (opOL2 x1 x2 )  = ((op Bo ) (evalOpE n Bo vars x1 ) (evalOpE n Bo vars x2 ) )
  
  inductionB : ((P  : (BooleanGroupTerm  → Set ))  → ((P eL ) → (((x1 x2  : BooleanGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : BooleanGroupTerm )  → (P x )))))
  inductionB p pel popl eL  = pel 
  
  inductionB p pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pel popl x1 ) (inductionB p pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClBooleanGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P eCl ) → (((x1 x2  : (ClBooleanGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClBooleanGroupTerm A ))  → (P x ))))))
  inductionCl _ p psing pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pecl popcl x1 ) (inductionCl _ p psing pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpBooleanGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P eOL ) → (((x1 x2  : (OpBooleanGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpBooleanGroupTerm n ))  → (P x ))))))
  inductionOp _ p pv peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv peol popol eOL  = peol 
  
  inductionOp _ p pv peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv peol popol x1 ) (inductionOp _ p pv peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpBooleanGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P eOL2 ) → (((x1 x2  : (OpBooleanGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpBooleanGroupTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 peol2 popol2 x2 ) )
  
  eL' : (  BooleanGroupTerm  )
  eL'  = eL 
  
  opL' : (  (BooleanGroupTerm   → (BooleanGroupTerm   → BooleanGroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (BooleanGroupTerm  → (Staged BooleanGroupTerm  ))
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  eCl' : ({A  : Set }  → (ClBooleanGroupTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClBooleanGroupTerm A )  → ((ClBooleanGroupTerm A )  → (ClBooleanGroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClBooleanGroupTerm A ) → (Staged (ClBooleanGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  eOL' : ({n  : Nat}  → (OpBooleanGroupTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpBooleanGroupTerm n )  → ((OpBooleanGroupTerm n )  → (OpBooleanGroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpBooleanGroupTerm n ) → (Staged (OpBooleanGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpBooleanGroupTerm2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpBooleanGroupTerm2 n A )  → ((OpBooleanGroupTerm2 n A )  → (OpBooleanGroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpBooleanGroupTerm2 n A ) → (Staged (OpBooleanGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
