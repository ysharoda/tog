
 module Unital  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Unital (A  : Set )  : Set where
    constructor UnitalC
    field
      e : A 
      op : (A  → (A  → A ))
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x ) 
  
  open Unital
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
  
  record Hom (A1 A2  : Set ) (Un1  : (Unital A1 )) (Un2  : (Unital A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-e : (  (hom (e Un1 )  ) ≡ (e Un2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Un1 ) x1 x2 ) ) ≡ ((op Un2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Un1  : (Unital A1 )) (Un2  : (Unital A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-e : (  (interp (e Un1 )  (e Un2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Un1 ) x1 x2 ) ((op Un2 ) y1 y2 ) )))) 
  
  data UnitalTerm  : Set where
    eL : UnitalTerm  
    opL : (UnitalTerm   → (UnitalTerm   → UnitalTerm  )) 
  
  data ClUnitalTerm (A  : Set )  : Set where
    sing : (A  → (ClUnitalTerm A ) )
    eCl : (ClUnitalTerm A ) 
    opCl : ((ClUnitalTerm A )  → ((ClUnitalTerm A )  → (ClUnitalTerm A ) )) 
  
  data OpUnitalTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpUnitalTerm n ) )
    eOL : (OpUnitalTerm n ) 
    opOL : ((OpUnitalTerm n )  → ((OpUnitalTerm n )  → (OpUnitalTerm n ) )) 
  
  data OpUnitalTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpUnitalTerm2 n A ) )
    sing2 : (A  → (OpUnitalTerm2 n A ) )
    eOL2 : (OpUnitalTerm2 n A ) 
    opOL2 : ((OpUnitalTerm2 n A )  → ((OpUnitalTerm2 n A )  → (OpUnitalTerm2 n A ) )) 
  
  simplifyB : (UnitalTerm  → UnitalTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB (opL x eL )  = x 
  
  simplifyB eL  = eL 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClUnitalTerm A ) → (ClUnitalTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ (opCl x eCl )  = x 
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpUnitalTerm n ) → (OpUnitalTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ (opOL x eOL )  = x 
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpUnitalTerm2 n A ) → (OpUnitalTerm2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x eOL2 )  = x 
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Unital A ) → (UnitalTerm  → A )))
  evalB Un eL  = (e Un ) 
  
  evalB Un (opL x1 x2 )  = ((op Un ) (evalB Un x1 ) (evalB Un x2 ) )
  
  evalCl : ({A  : Set }  → ((Unital A ) → ((ClUnitalTerm A ) → A )))
  evalCl Un (sing x1 )  = x1 
  
  evalCl Un eCl  = (e Un ) 
  
  evalCl Un (opCl x1 x2 )  = ((op Un ) (evalCl Un x1 ) (evalCl Un x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Unital A ) → ((Vec A n ) → ((OpUnitalTerm n ) → A ))))
  evalOp n Un vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Un vars eOL  = (e Un ) 
  
  evalOp n Un vars (opOL x1 x2 )  = ((op Un ) (evalOp n Un vars x1 ) (evalOp n Un vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Unital A ) → ((Vec A n ) → ((OpUnitalTerm2 n A ) → A ))))
  evalOpE n Un vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Un vars (sing2 x1 )  = x1 
  
  evalOpE n Un vars eOL2  = (e Un ) 
  
  evalOpE n Un vars (opOL2 x1 x2 )  = ((op Un ) (evalOpE n Un vars x1 ) (evalOpE n Un vars x2 ) )
  
  inductionB : ((P  : (UnitalTerm  → Set ))  → ((P eL ) → (((x1 x2  : UnitalTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : UnitalTerm )  → (P x )))))
  inductionB p pel popl eL  = pel 
  
  inductionB p pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pel popl x1 ) (inductionB p pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClUnitalTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P eCl ) → (((x1 x2  : (ClUnitalTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClUnitalTerm A ))  → (P x ))))))
  inductionCl _ p psing pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pecl popcl x1 ) (inductionCl _ p psing pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpUnitalTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P eOL ) → (((x1 x2  : (OpUnitalTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpUnitalTerm n ))  → (P x ))))))
  inductionOp _ p pv peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv peol popol eOL  = peol 
  
  inductionOp _ p pv peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv peol popol x1 ) (inductionOp _ p pv peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpUnitalTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P eOL2 ) → (((x1 x2  : (OpUnitalTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpUnitalTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 peol2 popol2 x2 ) )
  
  eL' : (  UnitalTerm  )
  eL'  = eL 
  
  opL' : (  (UnitalTerm   → (UnitalTerm   → UnitalTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (UnitalTerm  → (Staged UnitalTerm  ))
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  eCl' : ({A  : Set }  → (ClUnitalTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClUnitalTerm A )  → ((ClUnitalTerm A )  → (ClUnitalTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClUnitalTerm A ) → (Staged (ClUnitalTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  eOL' : ({n  : Nat}  → (OpUnitalTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpUnitalTerm n )  → ((OpUnitalTerm n )  → (OpUnitalTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpUnitalTerm n ) → (Staged (OpUnitalTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpUnitalTerm2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpUnitalTerm2 n A )  → ((OpUnitalTerm2 n A )  → (OpUnitalTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpUnitalTerm2 n A ) → (Staged (OpUnitalTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
