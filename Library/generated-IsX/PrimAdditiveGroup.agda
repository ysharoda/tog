
 module PrimAdditiveGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPrimAdditiveGroup (A  : Set ) (0ᵢ_  : A ) (*_  : (A  → (A  → A ))) (inv_  : (A  → A ))  : Set where
    constructor IsPrimAdditiveGroupC
    field
      lunit_0ᵢ_ : ({x  : A }  → (*_ 0ᵢ_ x ) ≡ x )
      runit_0ᵢ_ : ({x  : A }  → (*_ x 0ᵢ_ ) ≡ x )
      associative_*_ : ({x y z  : A }  → (*_ (*_ x y ) z ) ≡ (*_ x (*_ y z ) ))
      leftInverse_inv_op_0ᵢ_ : ({x  : A }  → (*_ x (inv_ x ) ) ≡ 0ᵢ_ )
      rightInverse_inv_op_0ᵢ_ : ({x  : A }  → (*_ (inv_ x ) x ) ≡ 0ᵢ_ )
      commutative_*_ : ({x y  : A }  → (*_ x y ) ≡ (*_ y x )) 
  
  record PrimAdditiveGroup (A  : Set )  : Set where
    constructor PrimAdditiveGroupC
    field
      0ᵢ_ : A 
      *_ : (A  → (A  → A ))
      inv_ : (A  → A )
      isPrimAdditiveGroup : (IsPrimAdditiveGroup A 0ᵢ_ *_ inv_ ) 
  
  open PrimAdditiveGroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0ᵢ_S : AS 
      *_S : (AS  → (AS  → AS ))
      inv_S : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0ᵢ_P : (Prod AP AP )
      *_P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      inv_P : ((Prod AP AP ) → (Prod AP AP ))
      lunit_0ᵢ_P : ({xP  : (Prod AP AP )}  → (*_P 0ᵢ_P xP ) ≡ xP )
      runit_0ᵢ_P : ({xP  : (Prod AP AP )}  → (*_P xP 0ᵢ_P ) ≡ xP )
      associative_*_P : ({xP yP zP  : (Prod AP AP )}  → (*_P (*_P xP yP ) zP ) ≡ (*_P xP (*_P yP zP ) ))
      leftInverse_inv_op_0ᵢ_P : ({xP  : (Prod AP AP )}  → (*_P xP (inv_P xP ) ) ≡ 0ᵢ_P )
      rightInverse_inv_op_0ᵢ_P : ({xP  : (Prod AP AP )}  → (*_P (inv_P xP ) xP ) ≡ 0ᵢ_P )
      commutative_*_P : ({xP yP  : (Prod AP AP )}  → (*_P xP yP ) ≡ (*_P yP xP )) 
  
  record Hom (A1 A2  : Set ) (Pr1  : (PrimAdditiveGroup A1 )) (Pr2  : (PrimAdditiveGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0_ : (  (hom (0ᵢ_ Pr1 )  ) ≡ (0ᵢ_ Pr2 ) )
      pres-*_ : ({x1  : A1} {x2  : A1}  → (hom ((*_ Pr1 ) x1 x2 ) ) ≡ ((*_ Pr2 ) (hom x1 ) (hom x2 ) ))
      pres-inv_ : ({x1  : A1}  → (hom ((inv_ Pr1 ) x1 ) ) ≡ ((inv_ Pr2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Pr1  : (PrimAdditiveGroup A1 )) (Pr2  : (PrimAdditiveGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0_ : (  (interp (0ᵢ_ Pr1 )  (0ᵢ_ Pr2 )  ))
      interp-*_ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((*_ Pr1 ) x1 x2 ) ((*_ Pr2 ) y1 y2 ) ))))
      interp-inv_ : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv_ Pr1 ) x1 ) ((inv_ Pr2 ) y1 ) ))) 
  
  data PrimAdditiveGroupTerm  : Set where
    0ᵢ_L : PrimAdditiveGroupTerm  
    *_L : (PrimAdditiveGroupTerm   → (PrimAdditiveGroupTerm   → PrimAdditiveGroupTerm  ))
    inv_L : (PrimAdditiveGroupTerm   → PrimAdditiveGroupTerm  ) 
  
  data ClPrimAdditiveGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClPrimAdditiveGroupTerm A ) )
    0ᵢ_Cl : (ClPrimAdditiveGroupTerm A ) 
    *_Cl : ((ClPrimAdditiveGroupTerm A )  → ((ClPrimAdditiveGroupTerm A )  → (ClPrimAdditiveGroupTerm A ) ))
    inv_Cl : ((ClPrimAdditiveGroupTerm A )  → (ClPrimAdditiveGroupTerm A ) ) 
  
  data OpPrimAdditiveGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPrimAdditiveGroupTerm n ) )
    0ᵢ_OL : (OpPrimAdditiveGroupTerm n ) 
    *_OL : ((OpPrimAdditiveGroupTerm n )  → ((OpPrimAdditiveGroupTerm n )  → (OpPrimAdditiveGroupTerm n ) ))
    inv_OL : ((OpPrimAdditiveGroupTerm n )  → (OpPrimAdditiveGroupTerm n ) ) 
  
  data OpPrimAdditiveGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPrimAdditiveGroupTerm2 n A ) )
    sing2 : (A  → (OpPrimAdditiveGroupTerm2 n A ) )
    0ᵢ_OL2 : (OpPrimAdditiveGroupTerm2 n A ) 
    *_OL2 : ((OpPrimAdditiveGroupTerm2 n A )  → ((OpPrimAdditiveGroupTerm2 n A )  → (OpPrimAdditiveGroupTerm2 n A ) ))
    inv_OL2 : ((OpPrimAdditiveGroupTerm2 n A )  → (OpPrimAdditiveGroupTerm2 n A ) ) 
  
  simplifyB : (PrimAdditiveGroupTerm  → PrimAdditiveGroupTerm )
  simplifyB (*_L 0ᵢ_L x )  = x 
  
  simplifyB (*_L x 0ᵢ_L )  = x 
  
  simplifyB 0ᵢ_L  = 0ᵢ_L 
  
  simplifyB (*_L x1 x2 )  = (*_L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (inv_L x1 )  = (inv_L (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClPrimAdditiveGroupTerm A ) → (ClPrimAdditiveGroupTerm A )))
  simplifyCl _ (*_Cl 0ᵢ_Cl x )  = x 
  
  simplifyCl _ (*_Cl x 0ᵢ_Cl )  = x 
  
  simplifyCl _ 0ᵢ_Cl  = 0ᵢ_Cl 
  
  simplifyCl _ (*_Cl x1 x2 )  = (*_Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (inv_Cl x1 )  = (inv_Cl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPrimAdditiveGroupTerm n ) → (OpPrimAdditiveGroupTerm n )))
  simplifyOp _ (*_OL 0ᵢ_OL x )  = x 
  
  simplifyOp _ (*_OL x 0ᵢ_OL )  = x 
  
  simplifyOp _ 0ᵢ_OL  = 0ᵢ_OL 
  
  simplifyOp _ (*_OL x1 x2 )  = (*_OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (inv_OL x1 )  = (inv_OL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPrimAdditiveGroupTerm2 n A ) → (OpPrimAdditiveGroupTerm2 n A )))
  simplifyOpE _ _ (*_OL2 0ᵢ_OL2 x )  = x 
  
  simplifyOpE _ _ (*_OL2 x 0ᵢ_OL2 )  = x 
  
  simplifyOpE _ _ 0ᵢ_OL2  = 0ᵢ_OL2 
  
  simplifyOpE _ _ (*_OL2 x1 x2 )  = (*_OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (inv_OL2 x1 )  = (inv_OL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PrimAdditiveGroup A ) → (PrimAdditiveGroupTerm  → A )))
  evalB Pr 0ᵢ_L  = (0ᵢ_ Pr ) 
  
  evalB Pr (*_L x1 x2 )  = ((*_ Pr ) (evalB Pr x1 ) (evalB Pr x2 ) )
  
  evalB Pr (inv_L x1 )  = ((inv_ Pr ) (evalB Pr x1 ) )
  
  evalCl : ({A  : Set }  → ((PrimAdditiveGroup A ) → ((ClPrimAdditiveGroupTerm A ) → A )))
  evalCl Pr (sing x1 )  = x1 
  
  evalCl Pr 0ᵢ_Cl  = (0ᵢ_ Pr ) 
  
  evalCl Pr (*_Cl x1 x2 )  = ((*_ Pr ) (evalCl Pr x1 ) (evalCl Pr x2 ) )
  
  evalCl Pr (inv_Cl x1 )  = ((inv_ Pr ) (evalCl Pr x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PrimAdditiveGroup A ) → ((Vec A n ) → ((OpPrimAdditiveGroupTerm n ) → A ))))
  evalOp n Pr vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Pr vars 0ᵢ_OL  = (0ᵢ_ Pr ) 
  
  evalOp n Pr vars (*_OL x1 x2 )  = ((*_ Pr ) (evalOp n Pr vars x1 ) (evalOp n Pr vars x2 ) )
  
  evalOp n Pr vars (inv_OL x1 )  = ((inv_ Pr ) (evalOp n Pr vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PrimAdditiveGroup A ) → ((Vec A n ) → ((OpPrimAdditiveGroupTerm2 n A ) → A ))))
  evalOpE n Pr vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Pr vars (sing2 x1 )  = x1 
  
  evalOpE n Pr vars 0ᵢ_OL2  = (0ᵢ_ Pr ) 
  
  evalOpE n Pr vars (*_OL2 x1 x2 )  = ((*_ Pr ) (evalOpE n Pr vars x1 ) (evalOpE n Pr vars x2 ) )
  
  evalOpE n Pr vars (inv_OL2 x1 )  = ((inv_ Pr ) (evalOpE n Pr vars x1 ) )
  
  inductionB : ((P  : (PrimAdditiveGroupTerm  → Set ))  → ((P 0ᵢ_L ) → (((x1 x2  : PrimAdditiveGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (*_L x1 x2 ) )))) → (((x1  : PrimAdditiveGroupTerm  )  → ((P x1 ) → (P (inv_L x1 ) ))) → ((x  : PrimAdditiveGroupTerm )  → (P x ))))))
  inductionB p p0_l p*_l pinv_l 0ᵢ_L  = p0_l 
  
  inductionB p p0_l p*_l pinv_l (*_L x1 x2 )  = (p*_l _ _ (inductionB p p0_l p*_l pinv_l x1 ) (inductionB p p0_l p*_l pinv_l x2 ) )
  
  inductionB p p0_l p*_l pinv_l (inv_L x1 )  = (pinv_l _ (inductionB p p0_l p*_l pinv_l x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClPrimAdditiveGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0ᵢ_Cl ) → (((x1 x2  : (ClPrimAdditiveGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*_Cl x1 x2 ) )))) → (((x1  : (ClPrimAdditiveGroupTerm A ) )  → ((P x1 ) → (P (inv_Cl x1 ) ))) → ((x  : (ClPrimAdditiveGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing p0_cl p*_cl pinv_cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0_cl p*_cl pinv_cl 0ᵢ_Cl  = p0_cl 
  
  inductionCl _ p psing p0_cl p*_cl pinv_cl (*_Cl x1 x2 )  = (p*_cl _ _ (inductionCl _ p psing p0_cl p*_cl pinv_cl x1 ) (inductionCl _ p psing p0_cl p*_cl pinv_cl x2 ) )
  
  inductionCl _ p psing p0_cl p*_cl pinv_cl (inv_Cl x1 )  = (pinv_cl _ (inductionCl _ p psing p0_cl p*_cl pinv_cl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpPrimAdditiveGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0ᵢ_OL ) → (((x1 x2  : (OpPrimAdditiveGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*_OL x1 x2 ) )))) → (((x1  : (OpPrimAdditiveGroupTerm n ) )  → ((P x1 ) → (P (inv_OL x1 ) ))) → ((x  : (OpPrimAdditiveGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv p0_ol p*_ol pinv_ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0_ol p*_ol pinv_ol 0ᵢ_OL  = p0_ol 
  
  inductionOp _ p pv p0_ol p*_ol pinv_ol (*_OL x1 x2 )  = (p*_ol _ _ (inductionOp _ p pv p0_ol p*_ol pinv_ol x1 ) (inductionOp _ p pv p0_ol p*_ol pinv_ol x2 ) )
  
  inductionOp _ p pv p0_ol p*_ol pinv_ol (inv_OL x1 )  = (pinv_ol _ (inductionOp _ p pv p0_ol p*_ol pinv_ol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPrimAdditiveGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0ᵢ_OL2 ) → (((x1 x2  : (OpPrimAdditiveGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*_OL2 x1 x2 ) )))) → (((x1  : (OpPrimAdditiveGroupTerm2 n A ) )  → ((P x1 ) → (P (inv_OL2 x1 ) ))) → ((x  : (OpPrimAdditiveGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 0ᵢ_OL2  = p0_ol2 
  
  inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (*_OL2 x1 x2 )  = (p*_ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 (inv_OL2 x1 )  = (pinv_ol2 _ (inductionOpE _ _ p pv2 psing2 p0_ol2 p*_ol2 pinv_ol2 x1 ) )
  
  0ᵢ_L' : (  PrimAdditiveGroupTerm  )
  0ᵢ_L'  = 0ᵢ_L 
  
  *_L' : (  (PrimAdditiveGroupTerm   → (PrimAdditiveGroupTerm   → PrimAdditiveGroupTerm  )))
  *_L' x1 x2  = (*_L x1 x2 )
  
  inv_L' : (  (PrimAdditiveGroupTerm   → PrimAdditiveGroupTerm  ))
  inv_L' x1  = (inv_L x1 )
  
  stageB : (PrimAdditiveGroupTerm  → (Staged PrimAdditiveGroupTerm  ))
  stageB 0ᵢ_L  = (Now 0ᵢ_L )
  
  stageB (*_L x1 x2 )  = (stage2 *_L' (codeLift2 *_L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (inv_L x1 )  = (stage1 inv_L' (codeLift1 inv_L' ) (stageB  x1 ) )
  
  0ᵢ_Cl' : ({A  : Set }  → (ClPrimAdditiveGroupTerm A ) )
  0ᵢ_Cl'  = 0ᵢ_Cl 
  
  *_Cl' : ({A  : Set }  → ((ClPrimAdditiveGroupTerm A )  → ((ClPrimAdditiveGroupTerm A )  → (ClPrimAdditiveGroupTerm A ) )))
  *_Cl' x1 x2  = (*_Cl x1 x2 )
  
  inv_Cl' : ({A  : Set }  → ((ClPrimAdditiveGroupTerm A )  → (ClPrimAdditiveGroupTerm A ) ))
  inv_Cl' x1  = (inv_Cl x1 )
  
  stageCl : ((A  : Set )  → ((ClPrimAdditiveGroupTerm A ) → (Staged (ClPrimAdditiveGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0ᵢ_Cl  = (Now 0ᵢ_Cl )
  
  stageCl _ (*_Cl x1 x2 )  = (stage2 *_Cl' (codeLift2 *_Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (inv_Cl x1 )  = (stage1 inv_Cl' (codeLift1 inv_Cl' ) ((stageCl _ ) x1 ) )
  
  0ᵢ_OL' : ({n  : Nat}  → (OpPrimAdditiveGroupTerm n ) )
  0ᵢ_OL'  = 0ᵢ_OL 
  
  *_OL' : ({n  : Nat}  → ((OpPrimAdditiveGroupTerm n )  → ((OpPrimAdditiveGroupTerm n )  → (OpPrimAdditiveGroupTerm n ) )))
  *_OL' x1 x2  = (*_OL x1 x2 )
  
  inv_OL' : ({n  : Nat}  → ((OpPrimAdditiveGroupTerm n )  → (OpPrimAdditiveGroupTerm n ) ))
  inv_OL' x1  = (inv_OL x1 )
  
  stageOp : ((n  : Nat)  → ((OpPrimAdditiveGroupTerm n ) → (Staged (OpPrimAdditiveGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0ᵢ_OL  = (Now 0ᵢ_OL )
  
  stageOp _ (*_OL x1 x2 )  = (stage2 *_OL' (codeLift2 *_OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (inv_OL x1 )  = (stage1 inv_OL' (codeLift1 inv_OL' ) ((stageOp _ ) x1 ) )
  
  0ᵢ_OL2' : ({n  : Nat } {A  : Set }  → (OpPrimAdditiveGroupTerm2 n A ) )
  0ᵢ_OL2'  = 0ᵢ_OL2 
  
  *_OL2' : ({n  : Nat } {A  : Set }  → ((OpPrimAdditiveGroupTerm2 n A )  → ((OpPrimAdditiveGroupTerm2 n A )  → (OpPrimAdditiveGroupTerm2 n A ) )))
  *_OL2' x1 x2  = (*_OL2 x1 x2 )
  
  inv_OL2' : ({n  : Nat } {A  : Set }  → ((OpPrimAdditiveGroupTerm2 n A )  → (OpPrimAdditiveGroupTerm2 n A ) ))
  inv_OL2' x1  = (inv_OL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPrimAdditiveGroupTerm2 n A ) → (Staged (OpPrimAdditiveGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0ᵢ_OL2  = (Now 0ᵢ_OL2 )
  
  stageOpE _ _ (*_OL2 x1 x2 )  = (stage2 *_OL2' (codeLift2 *_OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (inv_OL2 x1 )  = (stage1 inv_OL2' (codeLift1 inv_OL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0ᵢ_T : (Repr A ) 
      *_T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      inv_T : ((Repr A )  → (Repr A ) ) 
   
