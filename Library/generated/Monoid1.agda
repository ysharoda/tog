
 module Monoid1  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Monoid1 (A  : Set )  : Set where
    constructor Monoid1C
    field
      1ᵢ : A 
      op : (A  → (A  → A ))
      lunit_1ᵢ : ({x  : A }  → (op 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (op x 1ᵢ ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) )) 
  
  open Monoid1
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      1S : AS 
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      1P : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      lunit_1P : ({xP  : (Prod AP AP )}  → (opP 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (opP xP 1P ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) )) 
  
  record Hom (A1 A2  : Set ) (Mo1  : (Monoid1 A1 )) (Mo2  : (Monoid1 A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-1 : (  (hom (1ᵢ Mo1 )  ) ≡ (1ᵢ Mo2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mo1 ) x1 x2 ) ) ≡ ((op Mo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mo1  : (Monoid1 A1 )) (Mo2  : (Monoid1 A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-1 : (  (interp (1ᵢ Mo1 )  (1ᵢ Mo2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mo1 ) x1 x2 ) ((op Mo2 ) y1 y2 ) )))) 
  
  data Monoid1LTerm  : Set where
    1L : Monoid1LTerm  
    opL : (Monoid1LTerm   → (Monoid1LTerm   → Monoid1LTerm  )) 
  
  data ClMonoid1ClTerm (A  : Set )  : Set where
    sing : (A  → (ClMonoid1ClTerm A ) )
    1Cl : (ClMonoid1ClTerm A ) 
    opCl : ((ClMonoid1ClTerm A )  → ((ClMonoid1ClTerm A )  → (ClMonoid1ClTerm A ) )) 
  
  data OpMonoid1OLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMonoid1OLTerm n ) )
    1OL : (OpMonoid1OLTerm n ) 
    opOL : ((OpMonoid1OLTerm n )  → ((OpMonoid1OLTerm n )  → (OpMonoid1OLTerm n ) )) 
  
  data OpMonoid1OL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMonoid1OL2Term2 n A ) )
    sing2 : (A  → (OpMonoid1OL2Term2 n A ) )
    1OL2 : (OpMonoid1OL2Term2 n A ) 
    opOL2 : ((OpMonoid1OL2Term2 n A )  → ((OpMonoid1OL2Term2 n A )  → (OpMonoid1OL2Term2 n A ) )) 
  
  simplifyB : (Monoid1LTerm  → Monoid1LTerm )
  simplifyB (opL 1L x )  = x 
  
  simplifyB (opL x 1L )  = x 
  
  simplifyB 1L  = 1L 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMonoid1ClTerm A ) → (ClMonoid1ClTerm A )))
  simplifyCl _ (opCl 1Cl x )  = x 
  
  simplifyCl _ (opCl x 1Cl )  = x 
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMonoid1OLTerm n ) → (OpMonoid1OLTerm n )))
  simplifyOp _ (opOL 1OL x )  = x 
  
  simplifyOp _ (opOL x 1OL )  = x 
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMonoid1OL2Term2 n A ) → (OpMonoid1OL2Term2 n A )))
  simplifyOpE _ _ (opOL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Monoid1 A ) → (Monoid1LTerm  → A )))
  evalB Mo 1L  = (1ᵢ Mo ) 
  
  evalB Mo (opL x1 x2 )  = ((op Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalCl : ({A  : Set }  → ((Monoid1 A ) → ((ClMonoid1ClTerm A ) → A )))
  evalCl Mo (sing x1 )  = x1 
  
  evalCl Mo 1Cl  = (1ᵢ Mo ) 
  
  evalCl Mo (opCl x1 x2 )  = ((op Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Monoid1 A ) → ((Vec A n ) → ((OpMonoid1OLTerm n ) → A ))))
  evalOp n Mo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mo vars 1OL  = (1ᵢ Mo ) 
  
  evalOp n Mo vars (opOL x1 x2 )  = ((op Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Monoid1 A ) → ((Vec A n ) → ((OpMonoid1OL2Term2 n A ) → A ))))
  evalOpE n Mo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mo vars (sing2 x1 )  = x1 
  
  evalOpE n Mo vars 1OL2  = (1ᵢ Mo ) 
  
  evalOpE n Mo vars (opOL2 x1 x2 )  = ((op Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  inductionB : ((P  : (Monoid1LTerm  → Set ))  → ((P 1L ) → (((x1 x2  : Monoid1LTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : Monoid1LTerm )  → (P x )))))
  inductionB p p1l popl 1L  = p1l 
  
  inductionB p p1l popl (opL x1 x2 )  = (popl _ _ (inductionB p p1l popl x1 ) (inductionB p p1l popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMonoid1ClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 1Cl ) → (((x1 x2  : (ClMonoid1ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClMonoid1ClTerm A ))  → (P x ))))))
  inductionCl _ p psing p1cl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p1cl popcl 1Cl  = p1cl 
  
  inductionCl _ p psing p1cl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing p1cl popcl x1 ) (inductionCl _ p psing p1cl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMonoid1OLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 1OL ) → (((x1 x2  : (OpMonoid1OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpMonoid1OLTerm n ))  → (P x ))))))
  inductionOp _ p pv p1ol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p1ol popol 1OL  = p1ol 
  
  inductionOp _ p pv p1ol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv p1ol popol x1 ) (inductionOp _ p pv p1ol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMonoid1OL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 1OL2 ) → (((x1 x2  : (OpMonoid1OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpMonoid1OL2Term2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p1ol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 popol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p1ol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 p1ol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 p1ol2 popol2 x2 ) )
  
  1L' : (  Monoid1LTerm  )
  1L'  = 1L 
  
  opL' : (  (Monoid1LTerm   → (Monoid1LTerm   → Monoid1LTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (Monoid1LTerm  → (Staged Monoid1LTerm  ))
  stageB 1L  = (Now 1L )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  1Cl' : ({A  : Set }  → (ClMonoid1ClTerm A ) )
  1Cl'  = 1Cl 
  
  opCl' : ({A  : Set }  → ((ClMonoid1ClTerm A )  → ((ClMonoid1ClTerm A )  → (ClMonoid1ClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMonoid1ClTerm A ) → (Staged (ClMonoid1ClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  1OL' : ({n  : Nat}  → (OpMonoid1OLTerm n ) )
  1OL'  = 1OL 
  
  opOL' : ({n  : Nat}  → ((OpMonoid1OLTerm n )  → ((OpMonoid1OLTerm n )  → (OpMonoid1OLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMonoid1OLTerm n ) → (Staged (OpMonoid1OLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpMonoid1OL2Term2 n A ) )
  1OL2'  = 1OL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMonoid1OL2Term2 n A )  → ((OpMonoid1OL2Term2 n A )  → (OpMonoid1OL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMonoid1OL2Term2 n A ) → (Staged (OpMonoid1OL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      1T : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
