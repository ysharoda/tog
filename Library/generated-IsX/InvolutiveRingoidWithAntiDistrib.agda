
 module InvolutiveRingoidWithAntiDistrib  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsInvolutiveRingoidWithAntiDistrib (A  : Set ) (*  : (A  → (A  → A ))) (+  : (A  → (A  → A ))) (prim  : (A  → A ))  : Set where
    constructor IsInvolutiveRingoidWithAntiDistribC
    field
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) ))
      antidis_prim_+ : ({x y  : A }  → (prim (+ x y ) ) ≡ (+ (prim y ) (prim x ) ))
      antidis_prim_* : ({x y  : A }  → (prim (* x y ) ) ≡ (* (prim y ) (prim x ) )) 
  
  record InvolutiveRingoidWithAntiDistrib (A  : Set )  : Set where
    constructor InvolutiveRingoidWithAntiDistribC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      prim : (A  → A )
      isInvolutiveRingoidWithAntiDistrib : (IsInvolutiveRingoidWithAntiDistrib A (*) (+) prim ) 
  
  open InvolutiveRingoidWithAntiDistrib
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      +S : (AS  → (AS  → AS ))
      primS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      primP : ((Prod AP AP ) → (Prod AP AP ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) ))
      antidis_prim_+P : ({xP yP  : (Prod AP AP )}  → (primP (+P xP yP ) ) ≡ (+P (primP yP ) (primP xP ) ))
      antidis_prim_*P : ({xP yP  : (Prod AP AP )}  → (primP (*P xP yP ) ) ≡ (*P (primP yP ) (primP xP ) )) 
  
  record Hom (A1 A2  : Set ) (In1  : (InvolutiveRingoidWithAntiDistrib A1 )) (In2  : (InvolutiveRingoidWithAntiDistrib A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* In1 ) x1 x2 ) ) ≡ ((* In2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ In1 ) x1 x2 ) ) ≡ ((+ In2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim In1 ) x1 ) ) ≡ ((prim In2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InvolutiveRingoidWithAntiDistrib A1 )) (In2  : (InvolutiveRingoidWithAntiDistrib A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* In1 ) x1 x2 ) ((* In2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ In1 ) x1 x2 ) ((+ In2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim In1 ) x1 ) ((prim In2 ) y1 ) ))) 
  
  data InvolutiveRingoidWithAntiDistribTerm  : Set where
    *L : (InvolutiveRingoidWithAntiDistribTerm   → (InvolutiveRingoidWithAntiDistribTerm   → InvolutiveRingoidWithAntiDistribTerm  ))
    +L : (InvolutiveRingoidWithAntiDistribTerm   → (InvolutiveRingoidWithAntiDistribTerm   → InvolutiveRingoidWithAntiDistribTerm  ))
    primL : (InvolutiveRingoidWithAntiDistribTerm   → InvolutiveRingoidWithAntiDistribTerm  ) 
  
  data ClInvolutiveRingoidWithAntiDistribTerm (A  : Set )  : Set where
    sing : (A  → (ClInvolutiveRingoidWithAntiDistribTerm A ) )
    *Cl : ((ClInvolutiveRingoidWithAntiDistribTerm A )  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → (ClInvolutiveRingoidWithAntiDistribTerm A ) ))
    +Cl : ((ClInvolutiveRingoidWithAntiDistribTerm A )  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → (ClInvolutiveRingoidWithAntiDistribTerm A ) ))
    primCl : ((ClInvolutiveRingoidWithAntiDistribTerm A )  → (ClInvolutiveRingoidWithAntiDistribTerm A ) ) 
  
  data OpInvolutiveRingoidWithAntiDistribTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInvolutiveRingoidWithAntiDistribTerm n ) )
    *OL : ((OpInvolutiveRingoidWithAntiDistribTerm n )  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → (OpInvolutiveRingoidWithAntiDistribTerm n ) ))
    +OL : ((OpInvolutiveRingoidWithAntiDistribTerm n )  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → (OpInvolutiveRingoidWithAntiDistribTerm n ) ))
    primOL : ((OpInvolutiveRingoidWithAntiDistribTerm n )  → (OpInvolutiveRingoidWithAntiDistribTerm n ) ) 
  
  data OpInvolutiveRingoidWithAntiDistribTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )
    sing2 : (A  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )
    *OL2 : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) ))
    +OL2 : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) ))
    primOL2 : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) ) 
  
  simplifyB : (InvolutiveRingoidWithAntiDistribTerm  → InvolutiveRingoidWithAntiDistribTerm )
  simplifyB (+L (primL y ) (primL x ) )  = (primL (+L x y ) )
  
  simplifyB (*L (primL y ) (primL x ) )  = (primL (*L x y ) )
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInvolutiveRingoidWithAntiDistribTerm A ) → (ClInvolutiveRingoidWithAntiDistribTerm A )))
  simplifyCl _ (+Cl (primCl y ) (primCl x ) )  = (primCl (+Cl x y ) )
  
  simplifyCl _ (*Cl (primCl y ) (primCl x ) )  = (primCl (*Cl x y ) )
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInvolutiveRingoidWithAntiDistribTerm n ) → (OpInvolutiveRingoidWithAntiDistribTerm n )))
  simplifyOp _ (+OL (primOL y ) (primOL x ) )  = (primOL (+OL x y ) )
  
  simplifyOp _ (*OL (primOL y ) (primOL x ) )  = (primOL (*OL x y ) )
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A ) → (OpInvolutiveRingoidWithAntiDistribTerm2 n A )))
  simplifyOpE _ _ (+OL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (+OL2 x y ) )
  
  simplifyOpE _ _ (*OL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (*OL2 x y ) )
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InvolutiveRingoidWithAntiDistrib A ) → (InvolutiveRingoidWithAntiDistribTerm  → A )))
  evalB In (*L x1 x2 )  = ((* In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In (+L x1 x2 )  = ((+ In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalB In (primL x1 )  = ((prim In ) (evalB In x1 ) )
  
  evalCl : ({A  : Set }  → ((InvolutiveRingoidWithAntiDistrib A ) → ((ClInvolutiveRingoidWithAntiDistribTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (*Cl x1 x2 )  = ((* In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In (+Cl x1 x2 )  = ((+ In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalCl In (primCl x1 )  = ((prim In ) (evalCl In x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InvolutiveRingoidWithAntiDistrib A ) → ((Vec A n ) → ((OpInvolutiveRingoidWithAntiDistribTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (*OL x1 x2 )  = ((* In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars (+OL x1 x2 )  = ((+ In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOp n In vars (primOL x1 )  = ((prim In ) (evalOp n In vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InvolutiveRingoidWithAntiDistrib A ) → ((Vec A n ) → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (*OL2 x1 x2 )  = ((* In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars (+OL2 x1 x2 )  = ((+ In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  evalOpE n In vars (primOL2 x1 )  = ((prim In ) (evalOpE n In vars x1 ) )
  
  inductionB : ((P  : (InvolutiveRingoidWithAntiDistribTerm  → Set ))  → (((x1 x2  : InvolutiveRingoidWithAntiDistribTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : InvolutiveRingoidWithAntiDistribTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1  : InvolutiveRingoidWithAntiDistribTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : InvolutiveRingoidWithAntiDistribTerm )  → (P x ))))))
  inductionB p p*l p+l ppriml (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (primL x1 )  = (ppriml _ (inductionB p p*l p+l ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInvolutiveRingoidWithAntiDistribTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClInvolutiveRingoidWithAntiDistribTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClInvolutiveRingoidWithAntiDistribTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1  : (ClInvolutiveRingoidWithAntiDistribTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClInvolutiveRingoidWithAntiDistribTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p+cl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl pprimcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInvolutiveRingoidWithAntiDistribTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpInvolutiveRingoidWithAntiDistribTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpInvolutiveRingoidWithAntiDistribTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1  : (OpInvolutiveRingoidWithAntiDistribTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpInvolutiveRingoidWithAntiDistribTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p+ol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol pprimol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInvolutiveRingoidWithAntiDistribTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1  : (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpInvolutiveRingoidWithAntiDistribTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) )
  
  *L' : (  (InvolutiveRingoidWithAntiDistribTerm   → (InvolutiveRingoidWithAntiDistribTerm   → InvolutiveRingoidWithAntiDistribTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (InvolutiveRingoidWithAntiDistribTerm   → (InvolutiveRingoidWithAntiDistribTerm   → InvolutiveRingoidWithAntiDistribTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  primL' : (  (InvolutiveRingoidWithAntiDistribTerm   → InvolutiveRingoidWithAntiDistribTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (InvolutiveRingoidWithAntiDistribTerm  → (Staged InvolutiveRingoidWithAntiDistribTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  *Cl' : ({A  : Set }  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → (ClInvolutiveRingoidWithAntiDistribTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → (ClInvolutiveRingoidWithAntiDistribTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClInvolutiveRingoidWithAntiDistribTerm A )  → (ClInvolutiveRingoidWithAntiDistribTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClInvolutiveRingoidWithAntiDistribTerm A ) → (Staged (ClInvolutiveRingoidWithAntiDistribTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  *OL' : ({n  : Nat}  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → (OpInvolutiveRingoidWithAntiDistribTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → (OpInvolutiveRingoidWithAntiDistribTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpInvolutiveRingoidWithAntiDistribTerm n )  → (OpInvolutiveRingoidWithAntiDistribTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpInvolutiveRingoidWithAntiDistribTerm n ) → (Staged (OpInvolutiveRingoidWithAntiDistribTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A )  → (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInvolutiveRingoidWithAntiDistribTerm2 n A ) → (Staged (OpInvolutiveRingoidWithAntiDistribTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      primT : ((Repr A )  → (Repr A ) ) 
   
