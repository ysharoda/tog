
 module InvolutiveFixedPoint  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveFixedPoint (A  : Set ) (prim  : (A  → A )) (1ᵢ  : A )  : Set where
    constructor IsInvolutiveFixedPointC
    field
      fixes_prim_1ᵢ : (prim 1ᵢ ) ≡ 1ᵢ 
      involutive_prim : ({x  : A }  → (prim (prim x ) ) ≡ x ) 
  
  record InvolutiveFixedPoint (A  : Set )  : Set where
    constructor InvolutiveFixedPointC
    field
      prim : (A  → A )
      1ᵢ : A 
      isInvolutiveFixedPoint : (IsInvolutiveFixedPoint A prim 1ᵢ ) 
  
  open InvolutiveFixedPoint
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      1S : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      1P : (Prod AP AP )
      fixes_prim_1P : (primP 1P ) ≡ 1P 
      involutive_primP : ({xP  : (Prod AP AP )}  → (primP (primP xP ) ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveFixedPoint A1 )) (In2  : (InvolutiveFixedPoint A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
      pres-1 : (  (hom (1ᵢ In1 )  ) ≡ (1ᵢ In2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveFixedPoint A1 )) (In2  : (InvolutiveFixedPoint A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
      interp-1 : (  (interp (1ᵢ In1 )  (1ᵢ In2 )  )) 
  
  data InvolutiveFixedPointTerm  : Set where
    primL : (InvolutiveFixedPointTerm   → InvolutiveFixedPointTerm  )
    1L : InvolutiveFixedPointTerm   
  
  data ClInvolutiveFixedPointTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveFixedPointTerm A ) )
    primCl : ((ClInvolutiveFixedPointTerm A )  → (ClInvolutiveFixedPointTerm A ) )
    1Cl : (ClInvolutiveFixedPointTerm A )  
  
  data OpInvolutiveFixedPointTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveFixedPointTerm n ) )
    primOL : ((OpInvolutiveFixedPointTerm n )  → (OpInvolutiveFixedPointTerm n ) )
    1OL : (OpInvolutiveFixedPointTerm n )  
  
  data OpInvolutiveFixedPointTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveFixedPointTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveFixedPointTerm2 n A ) )
    primOL2 : ((OpInvolutiveFixedPointTerm2 n A )  → (OpInvolutiveFixedPointTerm2 n A ) )
    1OL2 : (OpInvolutiveFixedPointTerm2 n A )  
  
  simplifyB : (InvolutiveFixedPointTerm  → InvolutiveFixedPointTerm )
  simplifyB (primL 1L )  = 1L 
  
  simplifyB (primL (primL x ) )  = x 
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyCl : ((A  : Set )  → ((ClInvolutiveFixedPointTerm A ) → (ClInvolutiveFixedPointTerm A )))
  simplifyCl _ (primCl 1Cl )  = 1Cl 
  
  simplifyCl _ (primCl (primCl x ) )  = x 
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutiveFixedPointTerm n ) → (OpInvolutiveFixedPointTerm n )))
  simplifyOp _ (primOL 1OL )  = 1OL 
  
  simplifyOp _ (primOL (primOL x ) )  = x 
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveFixedPointTerm2 n A ) → (OpInvolutiveFixedPointTerm2 n A )))
  simplifyOpE _ _ (primOL2 1OL2 )  = 1OL2 
  
  simplifyOpE _ _ (primOL2 (primOL2 x ) )  = x 
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InvolutiveFixedPoint A ) → (InvolutiveFixedPointTerm  → A )))
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalB In 1L  = (1ᵢ In ) 
  
  evalCl : ({A  : Set }  → ((InvolutiveFixedPoint A ) → ((ClInvolutiveFixedPointTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalCl In 1Cl  = (1ᵢ In ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveFixedPoint A ) → ((Vec A n ) → ((OpInvolutiveFixedPointTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars 1OL  = (1ᵢ In ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveFixedPoint A ) → ((Vec A n ) → ((OpInvolutiveFixedPointTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars 1OL2  = (1ᵢ In ) 
  
  inductionB : ((P  : (InvolutiveFixedPointTerm  → Set ))  → (((x1  : InvolutiveFixedPointTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((P 1L ) → ((x  : InvolutiveFixedPointTerm )  → (P x )))))
  inductionB p ppriml p1l (primL x1 )  = (ppriml _ (inductionB p ppriml p1l x1 ) )
  
  inductionB p ppriml p1l 1L  = p1l 
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveFixedPointTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInvolutiveFixedPointTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((P 1Cl ) → ((x  : (ClInvolutiveFixedPointTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl p1cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl p1cl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl p1cl x1 ) )
  
  inductionCl _ p psing pprimcl p1cl 1Cl  = p1cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveFixedPointTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInvolutiveFixedPointTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((P 1OL ) → ((x  : (OpInvolutiveFixedPointTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol p1ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol p1ol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol p1ol x1 ) )
  
  inductionOp _ p pv pprimol p1ol 1OL  = p1ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveFixedPointTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInvolutiveFixedPointTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((P 1OL2 ) → ((x  : (OpInvolutiveFixedPointTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 p1ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p1ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p1ol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 p1ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p1ol2 1OL2  = p1ol2 
  
  primL' : (  (InvolutiveFixedPointTerm   → InvolutiveFixedPointTerm  ))
  primL' x1  = (primL x1 )
  
  1L' : (  InvolutiveFixedPointTerm  )
  1L'  = 1L 
  
  stageB : (InvolutiveFixedPointTerm  → (Staged InvolutiveFixedPointTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB 1L  = (Now 1L )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveFixedPointTerm A )  → (ClInvolutiveFixedPointTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  1Cl' : ({A  : Set }  → (ClInvolutiveFixedPointTerm A ) )
  1Cl'  = 1Cl 
  
  stageCl : ((A  : Set )  → ((ClInvolutiveFixedPointTerm A ) → (Staged (ClInvolutiveFixedPointTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveFixedPointTerm n )  → (OpInvolutiveFixedPointTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  1OL' : ({n  : Nat}  → (OpInvolutiveFixedPointTerm n ) )
  1OL'  = 1OL 
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveFixedPointTerm n ) → (Staged (OpInvolutiveFixedPointTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveFixedPointTerm2 n A )  → (OpInvolutiveFixedPointTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpInvolutiveFixedPointTerm2 n A ) )
  1OL2'  = 1OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveFixedPointTerm2 n A ) → (Staged (OpInvolutiveFixedPointTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      1T : (Repr A )  
   
