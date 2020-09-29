
 module NonassociativeNondistributiveRing  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record NonassociativeNondistributiveRing (A  : Set )  : Set where
    constructor NonassociativeNondistributiveRingC
    field
      * : (A  → (A  → A ))
      1ᵢ : A 
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      inv : (A  → A )
      leftInverse_inv_op_1ᵢ : ({x  : A }  → (* x (inv x ) ) ≡ 1ᵢ )
      rightInverse_inv_op_1ᵢ : ({x  : A }  → (* (inv x ) x ) ≡ 1ᵢ )
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x ))
      + : (A  → (A  → A )) 
  
  open NonassociativeNondistributiveRing
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      1S : AS 
      invS : (AS  → AS )
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      invP : ((Prod AP AP ) → (Prod AP AP ))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      leftInverse_inv_op_1P : ({xP  : (Prod AP AP )}  → (*P xP (invP xP ) ) ≡ 1P )
      rightInverse_inv_op_1P : ({xP  : (Prod AP AP )}  → (*P (invP xP ) xP ) ≡ 1P )
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP )) 
  
  record Hom (A1 A2  : Set ) (No1  : (NonassociativeNondistributiveRing A1 )) (No2  : (NonassociativeNondistributiveRing A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* No1 ) x1 x2 ) ) ≡ ((* No2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ No1 )  ) ≡ (1ᵢ No2 ) )
      pres-inv : ({x1  : A1}  → (hom ((inv No1 ) x1 ) ) ≡ ((inv No2 ) (hom x1 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ No1 ) x1 x2 ) ) ≡ ((+ No2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (No1  : (NonassociativeNondistributiveRing A1 )) (No2  : (NonassociativeNondistributiveRing A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* No1 ) x1 x2 ) ((* No2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ No1 )  (1ᵢ No2 )  ))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv No1 ) x1 ) ((inv No2 ) y1 ) )))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ No1 ) x1 x2 ) ((+ No2 ) y1 y2 ) )))) 
  
  data NonassociativeNondistributiveRingTerm  : Set where
    *L : (NonassociativeNondistributiveRingTerm   → (NonassociativeNondistributiveRingTerm   → NonassociativeNondistributiveRingTerm  ))
    1L : NonassociativeNondistributiveRingTerm  
    invL : (NonassociativeNondistributiveRingTerm   → NonassociativeNondistributiveRingTerm  )
    +L : (NonassociativeNondistributiveRingTerm   → (NonassociativeNondistributiveRingTerm   → NonassociativeNondistributiveRingTerm  )) 
  
  data ClNonassociativeNondistributiveRingTerm (A  : Set )  : Set where
    sing : (A  → (ClNonassociativeNondistributiveRingTerm A ) )
    *Cl : ((ClNonassociativeNondistributiveRingTerm A )  → ((ClNonassociativeNondistributiveRingTerm A )  → (ClNonassociativeNondistributiveRingTerm A ) ))
    1Cl : (ClNonassociativeNondistributiveRingTerm A ) 
    invCl : ((ClNonassociativeNondistributiveRingTerm A )  → (ClNonassociativeNondistributiveRingTerm A ) )
    +Cl : ((ClNonassociativeNondistributiveRingTerm A )  → ((ClNonassociativeNondistributiveRingTerm A )  → (ClNonassociativeNondistributiveRingTerm A ) )) 
  
  data OpNonassociativeNondistributiveRingTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpNonassociativeNondistributiveRingTerm n ) )
    *OL : ((OpNonassociativeNondistributiveRingTerm n )  → ((OpNonassociativeNondistributiveRingTerm n )  → (OpNonassociativeNondistributiveRingTerm n ) ))
    1OL : (OpNonassociativeNondistributiveRingTerm n ) 
    invOL : ((OpNonassociativeNondistributiveRingTerm n )  → (OpNonassociativeNondistributiveRingTerm n ) )
    +OL : ((OpNonassociativeNondistributiveRingTerm n )  → ((OpNonassociativeNondistributiveRingTerm n )  → (OpNonassociativeNondistributiveRingTerm n ) )) 
  
  data OpNonassociativeNondistributiveRingTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpNonassociativeNondistributiveRingTerm2 n A ) )
    sing2 : (A  → (OpNonassociativeNondistributiveRingTerm2 n A ) )
    *OL2 : ((OpNonassociativeNondistributiveRingTerm2 n A )  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → (OpNonassociativeNondistributiveRingTerm2 n A ) ))
    1OL2 : (OpNonassociativeNondistributiveRingTerm2 n A ) 
    invOL2 : ((OpNonassociativeNondistributiveRingTerm2 n A )  → (OpNonassociativeNondistributiveRingTerm2 n A ) )
    +OL2 : ((OpNonassociativeNondistributiveRingTerm2 n A )  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → (OpNonassociativeNondistributiveRingTerm2 n A ) )) 
  
  simplifyB : (NonassociativeNondistributiveRingTerm  → NonassociativeNondistributiveRingTerm )
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClNonassociativeNondistributiveRingTerm A ) → (ClNonassociativeNondistributiveRingTerm A )))
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpNonassociativeNondistributiveRingTerm n ) → (OpNonassociativeNondistributiveRingTerm n )))
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpNonassociativeNondistributiveRingTerm2 n A ) → (OpNonassociativeNondistributiveRingTerm2 n A )))
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((NonassociativeNondistributiveRing A ) → (NonassociativeNondistributiveRingTerm  → A )))
  evalB No (*L x1 x2 )  = ((* No ) (evalB No x1 ) (evalB No x2 ) )
  
  evalB No 1L  = (1ᵢ No ) 
  
  evalB No (invL x1 )  = ((inv No ) (evalB No x1 ) )
  
  evalB No (+L x1 x2 )  = ((+ No ) (evalB No x1 ) (evalB No x2 ) )
  
  evalCl : ({A  : Set }  → ((NonassociativeNondistributiveRing A ) → ((ClNonassociativeNondistributiveRingTerm A ) → A )))
  evalCl No (sing x1 )  = x1 
  
  evalCl No (*Cl x1 x2 )  = ((* No ) (evalCl No x1 ) (evalCl No x2 ) )
  
  evalCl No 1Cl  = (1ᵢ No ) 
  
  evalCl No (invCl x1 )  = ((inv No ) (evalCl No x1 ) )
  
  evalCl No (+Cl x1 x2 )  = ((+ No ) (evalCl No x1 ) (evalCl No x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((NonassociativeNondistributiveRing A ) → ((Vec A n ) → ((OpNonassociativeNondistributiveRingTerm n ) → A ))))
  evalOp n No vars (v x1 )  = (lookup vars x1 )
  
  evalOp n No vars (*OL x1 x2 )  = ((* No ) (evalOp n No vars x1 ) (evalOp n No vars x2 ) )
  
  evalOp n No vars 1OL  = (1ᵢ No ) 
  
  evalOp n No vars (invOL x1 )  = ((inv No ) (evalOp n No vars x1 ) )
  
  evalOp n No vars (+OL x1 x2 )  = ((+ No ) (evalOp n No vars x1 ) (evalOp n No vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((NonassociativeNondistributiveRing A ) → ((Vec A n ) → ((OpNonassociativeNondistributiveRingTerm2 n A ) → A ))))
  evalOpE n No vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n No vars (sing2 x1 )  = x1 
  
  evalOpE n No vars (*OL2 x1 x2 )  = ((* No ) (evalOpE n No vars x1 ) (evalOpE n No vars x2 ) )
  
  evalOpE n No vars 1OL2  = (1ᵢ No ) 
  
  evalOpE n No vars (invOL2 x1 )  = ((inv No ) (evalOpE n No vars x1 ) )
  
  evalOpE n No vars (+OL2 x1 x2 )  = ((+ No ) (evalOpE n No vars x1 ) (evalOpE n No vars x2 ) )
  
  inductionB : ((P  : (NonassociativeNondistributiveRingTerm  → Set ))  → (((x1 x2  : NonassociativeNondistributiveRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P 1L ) → (((x1  : NonassociativeNondistributiveRingTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → (((x1 x2  : NonassociativeNondistributiveRingTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : NonassociativeNondistributiveRingTerm )  → (P x )))))))
  inductionB p p*l p1l pinvl p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p1l pinvl p+l x1 ) (inductionB p p*l p1l pinvl p+l x2 ) )
  
  inductionB p p*l p1l pinvl p+l 1L  = p1l 
  
  inductionB p p*l p1l pinvl p+l (invL x1 )  = (pinvl _ (inductionB p p*l p1l pinvl p+l x1 ) )
  
  inductionB p p*l p1l pinvl p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p1l pinvl p+l x1 ) (inductionB p p*l p1l pinvl p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClNonassociativeNondistributiveRingTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClNonassociativeNondistributiveRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P 1Cl ) → (((x1  : (ClNonassociativeNondistributiveRingTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → (((x1 x2  : (ClNonassociativeNondistributiveRingTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClNonassociativeNondistributiveRingTerm A ))  → (P x ))))))))
  inductionCl _ p psing p*cl p1cl pinvcl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p1cl pinvcl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p1cl pinvcl p+cl x1 ) (inductionCl _ p psing p*cl p1cl pinvcl p+cl x2 ) )
  
  inductionCl _ p psing p*cl p1cl pinvcl p+cl 1Cl  = p1cl 
  
  inductionCl _ p psing p*cl p1cl pinvcl p+cl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing p*cl p1cl pinvcl p+cl x1 ) )
  
  inductionCl _ p psing p*cl p1cl pinvcl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p1cl pinvcl p+cl x1 ) (inductionCl _ p psing p*cl p1cl pinvcl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpNonassociativeNondistributiveRingTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpNonassociativeNondistributiveRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P 1OL ) → (((x1  : (OpNonassociativeNondistributiveRingTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → (((x1 x2  : (OpNonassociativeNondistributiveRingTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpNonassociativeNondistributiveRingTerm n ))  → (P x ))))))))
  inductionOp _ p pv p*ol p1ol pinvol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p1ol pinvol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p1ol pinvol p+ol x1 ) (inductionOp _ p pv p*ol p1ol pinvol p+ol x2 ) )
  
  inductionOp _ p pv p*ol p1ol pinvol p+ol 1OL  = p1ol 
  
  inductionOp _ p pv p*ol p1ol pinvol p+ol (invOL x1 )  = (pinvol _ (inductionOp _ p pv p*ol p1ol pinvol p+ol x1 ) )
  
  inductionOp _ p pv p*ol p1ol pinvol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p1ol pinvol p+ol x1 ) (inductionOp _ p pv p*ol p1ol pinvol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpNonassociativeNondistributiveRingTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpNonassociativeNondistributiveRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P 1OL2 ) → (((x1  : (OpNonassociativeNondistributiveRingTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → (((x1 x2  : (OpNonassociativeNondistributiveRingTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpNonassociativeNondistributiveRingTerm2 n A ))  → (P x )))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p1ol2 pinvol2 p+ol2 x2 ) )
  
  *L' : (  (NonassociativeNondistributiveRingTerm   → (NonassociativeNondistributiveRingTerm   → NonassociativeNondistributiveRingTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  1L' : (  NonassociativeNondistributiveRingTerm  )
  1L'  = 1L 
  
  invL' : (  (NonassociativeNondistributiveRingTerm   → NonassociativeNondistributiveRingTerm  ))
  invL' x1  = (invL x1 )
  
  +L' : (  (NonassociativeNondistributiveRingTerm   → (NonassociativeNondistributiveRingTerm   → NonassociativeNondistributiveRingTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (NonassociativeNondistributiveRingTerm  → (Staged NonassociativeNondistributiveRingTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClNonassociativeNondistributiveRingTerm A )  → ((ClNonassociativeNondistributiveRingTerm A )  → (ClNonassociativeNondistributiveRingTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClNonassociativeNondistributiveRingTerm A ) )
  1Cl'  = 1Cl 
  
  invCl' : ({A  : Set }  → ((ClNonassociativeNondistributiveRingTerm A )  → (ClNonassociativeNondistributiveRingTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  +Cl' : ({A  : Set }  → ((ClNonassociativeNondistributiveRingTerm A )  → ((ClNonassociativeNondistributiveRingTerm A )  → (ClNonassociativeNondistributiveRingTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClNonassociativeNondistributiveRingTerm A ) → (Staged (ClNonassociativeNondistributiveRingTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpNonassociativeNondistributiveRingTerm n )  → ((OpNonassociativeNondistributiveRingTerm n )  → (OpNonassociativeNondistributiveRingTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpNonassociativeNondistributiveRingTerm n ) )
  1OL'  = 1OL 
  
  invOL' : ({n  : Nat}  → ((OpNonassociativeNondistributiveRingTerm n )  → (OpNonassociativeNondistributiveRingTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  +OL' : ({n  : Nat}  → ((OpNonassociativeNondistributiveRingTerm n )  → ((OpNonassociativeNondistributiveRingTerm n )  → (OpNonassociativeNondistributiveRingTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpNonassociativeNondistributiveRingTerm n ) → (Staged (OpNonassociativeNondistributiveRingTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → (OpNonassociativeNondistributiveRingTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpNonassociativeNondistributiveRingTerm2 n A ) )
  1OL2'  = 1OL2 
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → (OpNonassociativeNondistributiveRingTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → ((OpNonassociativeNondistributiveRingTerm2 n A )  → (OpNonassociativeNondistributiveRingTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpNonassociativeNondistributiveRingTerm2 n A ) → (Staged (OpNonassociativeNondistributiveRingTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 
      invT : ((Repr A )  → (Repr A ) )
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
