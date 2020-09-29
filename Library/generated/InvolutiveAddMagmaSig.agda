
 module InvolutiveAddMagmaSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveAddMagmaSig (A  : Set )  : Set where
    constructor InvolutiveAddMagmaSigC
    field
      + : (A  → (A  → A ))
      prim : (A  → A ) 
  
  open InvolutiveAddMagmaSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
      primS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      primP : ((Prod AP AP ) → (Prod AP AP )) 
  
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveAddMagmaSig A1 )) (In2  : (InvolutiveAddMagmaSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ In1 ) x1 x2 ) ) ≡ ((+ In2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveAddMagmaSig A1 )) (In2  : (InvolutiveAddMagmaSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ In1 ) x1 x2 ) ((+ In2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) ))) 
  
  data InvolutiveAddMagmaSigTerm  : Set where
    +L : (InvolutiveAddMagmaSigTerm   → (InvolutiveAddMagmaSigTerm   → InvolutiveAddMagmaSigTerm  ))
    primL : (InvolutiveAddMagmaSigTerm   → InvolutiveAddMagmaSigTerm  ) 
  
  data ClInvolutiveAddMagmaSigTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveAddMagmaSigTerm A ) )
    +Cl : ((ClInvolutiveAddMagmaSigTerm A )  → ((ClInvolutiveAddMagmaSigTerm A )  → (ClInvolutiveAddMagmaSigTerm A ) ))
    primCl : ((ClInvolutiveAddMagmaSigTerm A )  → (ClInvolutiveAddMagmaSigTerm A ) ) 
  
  data OpInvolutiveAddMagmaSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveAddMagmaSigTerm n ) )
    +OL : ((OpInvolutiveAddMagmaSigTerm n )  → ((OpInvolutiveAddMagmaSigTerm n )  → (OpInvolutiveAddMagmaSigTerm n ) ))
    primOL : ((OpInvolutiveAddMagmaSigTerm n )  → (OpInvolutiveAddMagmaSigTerm n ) ) 
  
  data OpInvolutiveAddMagmaSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveAddMagmaSigTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveAddMagmaSigTerm2 n A ) )
    +OL2 : ((OpInvolutiveAddMagmaSigTerm2 n A )  → ((OpInvolutiveAddMagmaSigTerm2 n A )  → (OpInvolutiveAddMagmaSigTerm2 n A ) ))
    primOL2 : ((OpInvolutiveAddMagmaSigTerm2 n A )  → (OpInvolutiveAddMagmaSigTerm2 n A ) ) 
  
  simplifyB : (InvolutiveAddMagmaSigTerm  → InvolutiveAddMagmaSigTerm )
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInvolutiveAddMagmaSigTerm A ) → (ClInvolutiveAddMagmaSigTerm A )))
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutiveAddMagmaSigTerm n ) → (OpInvolutiveAddMagmaSigTerm n )))
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveAddMagmaSigTerm2 n A ) → (OpInvolutiveAddMagmaSigTerm2 n A )))
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InvolutiveAddMagmaSig A ) → (InvolutiveAddMagmaSigTerm  → A )))
  evalB In (+L x1 x2 )  = ((+ In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveAddMagmaSig A ) → ((ClInvolutiveAddMagmaSigTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (+Cl x1 x2 )  = ((+ In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveAddMagmaSig A ) → ((Vec A n ) → ((OpInvolutiveAddMagmaSigTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (+OL x1 x2 )  = ((+ In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveAddMagmaSig A ) → ((Vec A n ) → ((OpInvolutiveAddMagmaSigTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (+OL2 x1 x2 )  = ((+ In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InvolutiveAddMagmaSigTerm  → Set ))  → (((x1 x2  : InvolutiveAddMagmaSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1  : InvolutiveAddMagmaSigTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : InvolutiveAddMagmaSigTerm )  → (P x )))))
  inductionB p p+l ppriml (+L x1 x2 )  = (p+l _ _ (inductionB p p+l ppriml x1 ) (inductionB p p+l ppriml x2 ) )
  
  inductionB p p+l ppriml (primL x1 )  = (ppriml _ (inductionB p p+l ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveAddMagmaSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClInvolutiveAddMagmaSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1  : (ClInvolutiveAddMagmaSigTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClInvolutiveAddMagmaSigTerm A ))  → (P x ))))))
  inductionCl _ p psing p+cl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl pprimcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl pprimcl x1 ) (inductionCl _ p psing p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p+cl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p+cl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveAddMagmaSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpInvolutiveAddMagmaSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1  : (OpInvolutiveAddMagmaSigTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpInvolutiveAddMagmaSigTerm n ))  → (P x ))))))
  inductionOp _ p pv p+ol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol pprimol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol pprimol x1 ) (inductionOp _ p pv p+ol pprimol x2 ) )
  
  inductionOp _ p pv p+ol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p+ol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveAddMagmaSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpInvolutiveAddMagmaSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1  : (OpInvolutiveAddMagmaSigTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpInvolutiveAddMagmaSigTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p+ol2 pprimol2 x1 ) )
  
  +L' : (  (InvolutiveAddMagmaSigTerm   → (InvolutiveAddMagmaSigTerm   → InvolutiveAddMagmaSigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  primL' : (  (InvolutiveAddMagmaSigTerm   → InvolutiveAddMagmaSigTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (InvolutiveAddMagmaSigTerm  → (Staged InvolutiveAddMagmaSigTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  +Cl' : ({A  : Set }  → ((ClInvolutiveAddMagmaSigTerm A )  → ((ClInvolutiveAddMagmaSigTerm A )  → (ClInvolutiveAddMagmaSigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveAddMagmaSigTerm A )  → (ClInvolutiveAddMagmaSigTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveAddMagmaSigTerm A ) → (Staged (ClInvolutiveAddMagmaSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  +OL' : ({n  : Nat}  → ((OpInvolutiveAddMagmaSigTerm n )  → ((OpInvolutiveAddMagmaSigTerm n )  → (OpInvolutiveAddMagmaSigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveAddMagmaSigTerm n )  → (OpInvolutiveAddMagmaSigTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveAddMagmaSigTerm n ) → (Staged (OpInvolutiveAddMagmaSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveAddMagmaSigTerm2 n A )  → ((OpInvolutiveAddMagmaSigTerm2 n A )  → (OpInvolutiveAddMagmaSigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveAddMagmaSigTerm2 n A )  → (OpInvolutiveAddMagmaSigTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveAddMagmaSigTerm2 n A ) → (Staged (OpInvolutiveAddMagmaSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      primT : ((Repr A )  → (Repr A ) ) 
   
