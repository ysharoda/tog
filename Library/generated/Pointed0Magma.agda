
 module Pointed0Magma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Pointed0Magma (A  : Set )  : Set where
    constructor Pointed0MagmaC
    field
      0ᵢ : A 
      op : (A  → (A  → A )) 
  
  open Pointed0Magma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS 
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (Po1  : (Pointed0Magma A1 )) (Po2  : (Pointed0Magma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Po1 )  ) ≡ (0ᵢ Po2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Po1 ) x1 x2 ) ) ≡ ((op Po2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Po1  : (Pointed0Magma A1 )) (Po2  : (Pointed0Magma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Po1 )  (0ᵢ Po2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Po1 ) x1 x2 ) ((op Po2 ) y1 y2 ) )))) 
  
  data Pointed0MagmaTerm  : Set where
    0L : Pointed0MagmaTerm  
    opL : (Pointed0MagmaTerm   → (Pointed0MagmaTerm   → Pointed0MagmaTerm  )) 
  
  data ClPointed0MagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClPointed0MagmaTerm A ) )
    0Cl : (ClPointed0MagmaTerm A ) 
    opCl : ((ClPointed0MagmaTerm A )  → ((ClPointed0MagmaTerm A )  → (ClPointed0MagmaTerm A ) )) 
  
  data OpPointed0MagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointed0MagmaTerm n ) )
    0OL : (OpPointed0MagmaTerm n ) 
    opOL : ((OpPointed0MagmaTerm n )  → ((OpPointed0MagmaTerm n )  → (OpPointed0MagmaTerm n ) )) 
  
  data OpPointed0MagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointed0MagmaTerm2 n A ) )
    sing2 : (A  → (OpPointed0MagmaTerm2 n A ) )
    0OL2 : (OpPointed0MagmaTerm2 n A ) 
    opOL2 : ((OpPointed0MagmaTerm2 n A )  → ((OpPointed0MagmaTerm2 n A )  → (OpPointed0MagmaTerm2 n A ) )) 
  
  simplifyB : (Pointed0MagmaTerm  → Pointed0MagmaTerm )
  simplifyB 0L  = 0L 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClPointed0MagmaTerm A ) → (ClPointed0MagmaTerm A )))
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPointed0MagmaTerm n ) → (OpPointed0MagmaTerm n )))
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPointed0MagmaTerm2 n A ) → (OpPointed0MagmaTerm2 n A )))
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Pointed0Magma A ) → (Pointed0MagmaTerm  → A )))
  evalB Po 0L  = (0ᵢ Po ) 
  
  evalB Po (opL x1 x2 )  = ((op Po ) (evalB Po x1 ) (evalB Po x2 ) )
  
  evalCl : ({A  : Set }  → ((Pointed0Magma A ) → ((ClPointed0MagmaTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po 0Cl  = (0ᵢ Po ) 
  
  evalCl Po (opCl x1 x2 )  = ((op Po ) (evalCl Po x1 ) (evalCl Po x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Pointed0Magma A ) → ((Vec A n ) → ((OpPointed0MagmaTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars 0OL  = (0ᵢ Po ) 
  
  evalOp n Po vars (opOL x1 x2 )  = ((op Po ) (evalOp n Po vars x1 ) (evalOp n Po vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Pointed0Magma A ) → ((Vec A n ) → ((OpPointed0MagmaTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars 0OL2  = (0ᵢ Po ) 
  
  evalOpE n Po vars (opOL2 x1 x2 )  = ((op Po ) (evalOpE n Po vars x1 ) (evalOpE n Po vars x2 ) )
  
  inductionB : ((P  : (Pointed0MagmaTerm  → Set ))  → ((P 0L ) → (((x1 x2  : Pointed0MagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : Pointed0MagmaTerm )  → (P x )))))
  inductionB p p0l popl 0L  = p0l 
  
  inductionB p p0l popl (opL x1 x2 )  = (popl _ _ (inductionB p p0l popl x1 ) (inductionB p p0l popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClPointed0MagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClPointed0MagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClPointed0MagmaTerm A ))  → (P x ))))))
  inductionCl _ p psing p0cl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl popcl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing p0cl popcl x1 ) (inductionCl _ p psing p0cl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpPointed0MagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpPointed0MagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpPointed0MagmaTerm n ))  → (P x ))))))
  inductionOp _ p pv p0ol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol popol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv p0ol popol x1 ) (inductionOp _ p pv p0ol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointed0MagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpPointed0MagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpPointed0MagmaTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 popol2 x2 ) )
  
  0L' : (  Pointed0MagmaTerm  )
  0L'  = 0L 
  
  opL' : (  (Pointed0MagmaTerm   → (Pointed0MagmaTerm   → Pointed0MagmaTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (Pointed0MagmaTerm  → (Staged Pointed0MagmaTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClPointed0MagmaTerm A ) )
  0Cl'  = 0Cl 
  
  opCl' : ({A  : Set }  → ((ClPointed0MagmaTerm A )  → ((ClPointed0MagmaTerm A )  → (ClPointed0MagmaTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClPointed0MagmaTerm A ) → (Staged (ClPointed0MagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpPointed0MagmaTerm n ) )
  0OL'  = 0OL 
  
  opOL' : ({n  : Nat}  → ((OpPointed0MagmaTerm n )  → ((OpPointed0MagmaTerm n )  → (OpPointed0MagmaTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpPointed0MagmaTerm n ) → (Staged (OpPointed0MagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpPointed0MagmaTerm2 n A ) )
  0OL2'  = 0OL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpPointed0MagmaTerm2 n A )  → ((OpPointed0MagmaTerm2 n A )  → (OpPointed0MagmaTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointed0MagmaTerm2 n A ) → (Staged (OpPointed0MagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
