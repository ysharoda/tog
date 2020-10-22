
 module JacobianIdentity  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsJacobianIdentity (A  : Set ) (0ᵢ  : A ) (+  : (A  → (A  → A ))) (*  : (A  → (A  → A )))  : Set where
    constructor IsJacobianIdentityC
    field
      jacobian_*_+ : ({x y z  : A }  → (+ (+ (* x (* y z ) ) (* y (* z x ) ) ) (* z (* x y ) ) )  ≡ 0ᵢ ) 
  
  record JacobianIdentity (A  : Set )  : Set where
    constructor JacobianIdentityC
    field
      0ᵢ : A 
      + : (A  → (A  → A ))
      * : (A  → (A  → A ))
      isJacobianIdentity : (IsJacobianIdentity A 0ᵢ (+) (*) ) 
  
  open JacobianIdentity
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS 
      +S : (AS  → (AS  → AS ))
      *S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP )
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      jacobian_*_+P : ({xP yP zP  : (Prod AP AP )}  → (+P (+P (*P xP (*P yP zP ) ) (*P yP (*P zP xP ) ) ) (*P zP (*P xP yP ) ) )  ≡ 0P ) 
  
  record Hom (A1 A2  : Set ) (Ja1  : (JacobianIdentity A1 )) (Ja2  : (JacobianIdentity A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Ja1 )  ) ≡ (0ᵢ Ja2 ) )
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ja1 ) x1 x2 ) ) ≡ ((+ Ja2 ) (hom x1 ) (hom x2 ) ))
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ja1 ) x1 x2 ) ) ≡ ((* Ja2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ja1  : (JacobianIdentity A1 )) (Ja2  : (JacobianIdentity A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Ja1 )  (0ᵢ Ja2 )  ))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ja1 ) x1 x2 ) ((+ Ja2 ) y1 y2 ) ))))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ja1 ) x1 x2 ) ((* Ja2 ) y1 y2 ) )))) 
  
  data JacobianIdentityTerm  : Set where
    0L : JacobianIdentityTerm  
    +L : (JacobianIdentityTerm   → (JacobianIdentityTerm   → JacobianIdentityTerm  ))
    *L : (JacobianIdentityTerm   → (JacobianIdentityTerm   → JacobianIdentityTerm  )) 
  
  data ClJacobianIdentityTerm (A  : Set )  : Set where
    sing : (A  → (ClJacobianIdentityTerm A ) )
    0Cl : (ClJacobianIdentityTerm A ) 
    +Cl : ((ClJacobianIdentityTerm A )  → ((ClJacobianIdentityTerm A )  → (ClJacobianIdentityTerm A ) ))
    *Cl : ((ClJacobianIdentityTerm A )  → ((ClJacobianIdentityTerm A )  → (ClJacobianIdentityTerm A ) )) 
  
  data OpJacobianIdentityTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpJacobianIdentityTerm n ) )
    0OL : (OpJacobianIdentityTerm n ) 
    +OL : ((OpJacobianIdentityTerm n )  → ((OpJacobianIdentityTerm n )  → (OpJacobianIdentityTerm n ) ))
    *OL : ((OpJacobianIdentityTerm n )  → ((OpJacobianIdentityTerm n )  → (OpJacobianIdentityTerm n ) )) 
  
  data OpJacobianIdentityTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpJacobianIdentityTerm2 n A ) )
    sing2 : (A  → (OpJacobianIdentityTerm2 n A ) )
    0OL2 : (OpJacobianIdentityTerm2 n A ) 
    +OL2 : ((OpJacobianIdentityTerm2 n A )  → ((OpJacobianIdentityTerm2 n A )  → (OpJacobianIdentityTerm2 n A ) ))
    *OL2 : ((OpJacobianIdentityTerm2 n A )  → ((OpJacobianIdentityTerm2 n A )  → (OpJacobianIdentityTerm2 n A ) )) 
  
  simplifyB : (JacobianIdentityTerm  → JacobianIdentityTerm )
  simplifyB 0L  = 0L 
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClJacobianIdentityTerm A ) → (ClJacobianIdentityTerm A )))
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpJacobianIdentityTerm n ) → (OpJacobianIdentityTerm n )))
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpJacobianIdentityTerm2 n A ) → (OpJacobianIdentityTerm2 n A )))
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((JacobianIdentity A ) → (JacobianIdentityTerm  → A )))
  evalB Ja 0L  = (0ᵢ Ja ) 
  
  evalB Ja (+L x1 x2 )  = ((+ Ja ) (evalB Ja x1 ) (evalB Ja x2 ) )
  
  evalB Ja (*L x1 x2 )  = ((* Ja ) (evalB Ja x1 ) (evalB Ja x2 ) )
  
  evalCl : ({A  : Set }  → ((JacobianIdentity A ) → ((ClJacobianIdentityTerm A ) → A )))
  evalCl Ja (sing x1 )  = x1 
  
  evalCl Ja 0Cl  = (0ᵢ Ja ) 
  
  evalCl Ja (+Cl x1 x2 )  = ((+ Ja ) (evalCl Ja x1 ) (evalCl Ja x2 ) )
  
  evalCl Ja (*Cl x1 x2 )  = ((* Ja ) (evalCl Ja x1 ) (evalCl Ja x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((JacobianIdentity A ) → ((Vec A n ) → ((OpJacobianIdentityTerm n ) → A ))))
  evalOp n Ja vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ja vars 0OL  = (0ᵢ Ja ) 
  
  evalOp n Ja vars (+OL x1 x2 )  = ((+ Ja ) (evalOp n Ja vars x1 ) (evalOp n Ja vars x2 ) )
  
  evalOp n Ja vars (*OL x1 x2 )  = ((* Ja ) (evalOp n Ja vars x1 ) (evalOp n Ja vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((JacobianIdentity A ) → ((Vec A n ) → ((OpJacobianIdentityTerm2 n A ) → A ))))
  evalOpE n Ja vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ja vars (sing2 x1 )  = x1 
  
  evalOpE n Ja vars 0OL2  = (0ᵢ Ja ) 
  
  evalOpE n Ja vars (+OL2 x1 x2 )  = ((+ Ja ) (evalOpE n Ja vars x1 ) (evalOpE n Ja vars x2 ) )
  
  evalOpE n Ja vars (*OL2 x1 x2 )  = ((* Ja ) (evalOpE n Ja vars x1 ) (evalOpE n Ja vars x2 ) )
  
  inductionB : ((P  : (JacobianIdentityTerm  → Set ))  → ((P 0L ) → (((x1 x2  : JacobianIdentityTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1 x2  : JacobianIdentityTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : JacobianIdentityTerm )  → (P x ))))))
  inductionB p p0l p+l p*l 0L  = p0l 
  
  inductionB p p0l p+l p*l (+L x1 x2 )  = (p+l _ _ (inductionB p p0l p+l p*l x1 ) (inductionB p p0l p+l p*l x2 ) )
  
  inductionB p p0l p+l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p0l p+l p*l x1 ) (inductionB p p0l p+l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClJacobianIdentityTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClJacobianIdentityTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1 x2  : (ClJacobianIdentityTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClJacobianIdentityTerm A ))  → (P x )))))))
  inductionCl _ p psing p0cl p+cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl p+cl p*cl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl p+cl p*cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p0cl p+cl p*cl x1 ) (inductionCl _ p psing p0cl p+cl p*cl x2 ) )
  
  inductionCl _ p psing p0cl p+cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p0cl p+cl p*cl x1 ) (inductionCl _ p psing p0cl p+cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpJacobianIdentityTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpJacobianIdentityTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1 x2  : (OpJacobianIdentityTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpJacobianIdentityTerm n ))  → (P x )))))))
  inductionOp _ p pv p0ol p+ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol p+ol p*ol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol p+ol p*ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p0ol p+ol p*ol x1 ) (inductionOp _ p pv p0ol p+ol p*ol x2 ) )
  
  inductionOp _ p pv p0ol p+ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p0ol p+ol p*ol x1 ) (inductionOp _ p pv p0ol p+ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpJacobianIdentityTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpJacobianIdentityTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1 x2  : (OpJacobianIdentityTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpJacobianIdentityTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 p+ol2 p*ol2 x2 ) )
  
  0L' : (  JacobianIdentityTerm  )
  0L'  = 0L 
  
  +L' : (  (JacobianIdentityTerm   → (JacobianIdentityTerm   → JacobianIdentityTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  *L' : (  (JacobianIdentityTerm   → (JacobianIdentityTerm   → JacobianIdentityTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (JacobianIdentityTerm  → (Staged JacobianIdentityTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClJacobianIdentityTerm A ) )
  0Cl'  = 0Cl 
  
  +Cl' : ({A  : Set }  → ((ClJacobianIdentityTerm A )  → ((ClJacobianIdentityTerm A )  → (ClJacobianIdentityTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  *Cl' : ({A  : Set }  → ((ClJacobianIdentityTerm A )  → ((ClJacobianIdentityTerm A )  → (ClJacobianIdentityTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClJacobianIdentityTerm A ) → (Staged (ClJacobianIdentityTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpJacobianIdentityTerm n ) )
  0OL'  = 0OL 
  
  +OL' : ({n  : Nat}  → ((OpJacobianIdentityTerm n )  → ((OpJacobianIdentityTerm n )  → (OpJacobianIdentityTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  *OL' : ({n  : Nat}  → ((OpJacobianIdentityTerm n )  → ((OpJacobianIdentityTerm n )  → (OpJacobianIdentityTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpJacobianIdentityTerm n ) → (Staged (OpJacobianIdentityTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpJacobianIdentityTerm2 n A ) )
  0OL2'  = 0OL2 
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpJacobianIdentityTerm2 n A )  → ((OpJacobianIdentityTerm2 n A )  → (OpJacobianIdentityTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpJacobianIdentityTerm2 n A )  → ((OpJacobianIdentityTerm2 n A )  → (OpJacobianIdentityTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpJacobianIdentityTerm2 n A ) → (Staged (OpJacobianIdentityTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
