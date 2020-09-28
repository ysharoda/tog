module InvolutiveRingoidSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InvolutiveRingoidSig (A  : Set )  : Set where
    constructor InvolutiveRingoidSigC
    field
      prim : (A  → A )
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
  open InvolutiveRingoidSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveRingoidSig A1 )) (In2  : (InvolutiveRingoidSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* In1 ) x1 x2 ) ) ≡ ((* In2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ In1 ) x1 x2 ) ) ≡ ((+ In2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveRingoidSig A1 )) (In2  : (InvolutiveRingoidSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) )))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* In1 ) x1 x2 ) ((* In2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ In1 ) x1 x2 ) ((+ In2 ) y1 y2 ) ))))
  data InvolutiveRingoidSigTerm  : Set where
    primL : (InvolutiveRingoidSigTerm   → InvolutiveRingoidSigTerm  )
    *L : (InvolutiveRingoidSigTerm   → (InvolutiveRingoidSigTerm   → InvolutiveRingoidSigTerm  ))
    +L : (InvolutiveRingoidSigTerm   → (InvolutiveRingoidSigTerm   → InvolutiveRingoidSigTerm  ))
  data ClInvolutiveRingoidSigTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveRingoidSigTerm A ) )
    primCl : ((ClInvolutiveRingoidSigTerm A )  → (ClInvolutiveRingoidSigTerm A ) )
    *Cl : ((ClInvolutiveRingoidSigTerm A )  → ((ClInvolutiveRingoidSigTerm A )  → (ClInvolutiveRingoidSigTerm A ) ))
    +Cl : ((ClInvolutiveRingoidSigTerm A )  → ((ClInvolutiveRingoidSigTerm A )  → (ClInvolutiveRingoidSigTerm A ) ))
  data OpInvolutiveRingoidSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveRingoidSigTerm n ) )
    primOL : ((OpInvolutiveRingoidSigTerm n )  → (OpInvolutiveRingoidSigTerm n ) )
    *OL : ((OpInvolutiveRingoidSigTerm n )  → ((OpInvolutiveRingoidSigTerm n )  → (OpInvolutiveRingoidSigTerm n ) ))
    +OL : ((OpInvolutiveRingoidSigTerm n )  → ((OpInvolutiveRingoidSigTerm n )  → (OpInvolutiveRingoidSigTerm n ) ))
  data OpInvolutiveRingoidSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveRingoidSigTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveRingoidSigTerm2 n A ) )
    primOL2 : ((OpInvolutiveRingoidSigTerm2 n A )  → (OpInvolutiveRingoidSigTerm2 n A ) )
    *OL2 : ((OpInvolutiveRingoidSigTerm2 n A )  → ((OpInvolutiveRingoidSigTerm2 n A )  → (OpInvolutiveRingoidSigTerm2 n A ) ))
    +OL2 : ((OpInvolutiveRingoidSigTerm2 n A )  → ((OpInvolutiveRingoidSigTerm2 n A )  → (OpInvolutiveRingoidSigTerm2 n A ) ))
  evalB : ({A  : Set }  → ((InvolutiveRingoidSig A ) → (InvolutiveRingoidSigTerm  → A )))
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalB In (*L x1 x2 )  = ((* In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In (+L x1 x2 )  = ((+ In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveRingoidSig A ) → ((ClInvolutiveRingoidSigTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalCl In (*Cl x1 x2 )  = ((* In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In (+Cl x1 x2 )  = ((+ In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveRingoidSig A ) → ((Vec A n ) → ((OpInvolutiveRingoidSigTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars (*OL x1 x2 )  = ((* In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars (+OL x1 x2 )  = ((+ In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveRingoidSig A ) → ((Vec A n ) → ((OpInvolutiveRingoidSigTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars (*OL2 x1 x2 )  = ((* In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars (+OL2 x1 x2 )  = ((+ In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  inductionB : ((P  : (InvolutiveRingoidSigTerm  → Set ))  → (((x1  : InvolutiveRingoidSigTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : InvolutiveRingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : InvolutiveRingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : InvolutiveRingoidSigTerm )  → (P x ))))))
  inductionB p ppriml p*l p+l (primL x1 )  = (ppriml _ (inductionB p ppriml p*l p+l x1 ) )
  
  inductionB p ppriml p*l p+l (*L x1 x2 )  = (p*l _ _ (inductionB p ppriml p*l p+l x1 ) (inductionB p ppriml p*l p+l x2 ) )
  
  inductionB p ppriml p*l p+l (+L x1 x2 )  = (p+l _ _ (inductionB p ppriml p*l p+l x1 ) (inductionB p ppriml p*l p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveRingoidSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInvolutiveRingoidSigTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClInvolutiveRingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClInvolutiveRingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClInvolutiveRingoidSigTerm A ))  → (P x )))))))
  inductionCl _ p psing pprimcl p*cl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl p*cl p+cl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl p*cl p+cl x1 ) )
  
  inductionCl _ p psing pprimcl p*cl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing pprimcl p*cl p+cl x1 ) (inductionCl _ p psing pprimcl p*cl p+cl x2 ) )
  
  inductionCl _ p psing pprimcl p*cl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing pprimcl p*cl p+cl x1 ) (inductionCl _ p psing pprimcl p*cl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveRingoidSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInvolutiveRingoidSigTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpInvolutiveRingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpInvolutiveRingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpInvolutiveRingoidSigTerm n ))  → (P x )))))))
  inductionOp _ p pv pprimol p*ol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol p*ol p+ol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol p*ol p+ol x1 ) )
  
  inductionOp _ p pv pprimol p*ol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv pprimol p*ol p+ol x1 ) (inductionOp _ p pv pprimol p*ol p+ol x2 ) )
  
  inductionOp _ p pv pprimol p*ol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv pprimol p*ol p+ol x1 ) (inductionOp _ p pv pprimol p*ol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveRingoidSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInvolutiveRingoidSigTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpInvolutiveRingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpInvolutiveRingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpInvolutiveRingoidSigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 p*ol2 p+ol2 x2 ) )
  
  primL' : (  (InvolutiveRingoidSigTerm   → InvolutiveRingoidSigTerm  ))
  primL' x1  = (primL x1 )
  
  *L' : (  (InvolutiveRingoidSigTerm   → (InvolutiveRingoidSigTerm   → InvolutiveRingoidSigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (InvolutiveRingoidSigTerm   → (InvolutiveRingoidSigTerm   → InvolutiveRingoidSigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (InvolutiveRingoidSigTerm  → (Staged InvolutiveRingoidSigTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveRingoidSigTerm A )  → (ClInvolutiveRingoidSigTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  *Cl' : ({A  : Set }  → ((ClInvolutiveRingoidSigTerm A )  → ((ClInvolutiveRingoidSigTerm A )  → (ClInvolutiveRingoidSigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClInvolutiveRingoidSigTerm A )  → ((ClInvolutiveRingoidSigTerm A )  → (ClInvolutiveRingoidSigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveRingoidSigTerm A ) → (Staged (ClInvolutiveRingoidSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveRingoidSigTerm n )  → (OpInvolutiveRingoidSigTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  *OL' : ({n  : Nat}  → ((OpInvolutiveRingoidSigTerm n )  → ((OpInvolutiveRingoidSigTerm n )  → (OpInvolutiveRingoidSigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpInvolutiveRingoidSigTerm n )  → ((OpInvolutiveRingoidSigTerm n )  → (OpInvolutiveRingoidSigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveRingoidSigTerm n ) → (Staged (OpInvolutiveRingoidSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingoidSigTerm2 n A )  → (OpInvolutiveRingoidSigTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingoidSigTerm2 n A )  → ((OpInvolutiveRingoidSigTerm2 n A )  → (OpInvolutiveRingoidSigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingoidSigTerm2 n A )  → ((OpInvolutiveRingoidSigTerm2 n A )  → (OpInvolutiveRingoidSigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveRingoidSigTerm2 n A ) → (Staged (OpInvolutiveRingoidSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))