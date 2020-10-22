
 module AbelianGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAbelianGroup (A  : Set ) (1ᵢ  : A ) (*  : (A  → (A  → A ))) (inv  : (A  → A ))  : Set where
    constructor IsAbelianGroupC
    field
      lunit_1ᵢ : ({x  : A }  → (* 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (* x 1ᵢ ) ≡ x )
      associative_* : ({x y z  : A }  → (* (* x y ) z ) ≡ (* x (* y z ) ))
      leftInverse_inv_op_1ᵢ : ({x  : A }  → (* x (inv x ) ) ≡ 1ᵢ )
      rightInverse_inv_op_1ᵢ : ({x  : A }  → (* (inv x ) x ) ≡ 1ᵢ )
      commutative_* : ({x y  : A }  → (* x y ) ≡ (* y x )) 
  
  record AbelianGroup (A  : Set )  : Set where
    constructor AbelianGroupC
    field
      1ᵢ : A 
      * : (A  → (A  → A ))
      inv : (A  → A )
      isAbelianGroup : (IsAbelianGroup A 1ᵢ (*) inv ) 
  
  open AbelianGroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      1S : AS 
      *S : (AS  → (AS  → AS ))
      invS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      1P : (Prod AP AP )
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      invP : ((Prod AP AP ) → (Prod AP AP ))
      lunit_1P : ({xP  : (Prod AP AP )}  → (*P 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (*P xP 1P ) ≡ xP )
      associative_*P : ({xP yP zP  : (Prod AP AP )}  → (*P (*P xP yP ) zP ) ≡ (*P xP (*P yP zP ) ))
      leftInverse_inv_op_1P : ({xP  : (Prod AP AP )}  → (*P xP (invP xP ) ) ≡ 1P )
      rightInverse_inv_op_1P : ({xP  : (Prod AP AP )}  → (*P (invP xP ) xP ) ≡ 1P )
      commutative_*P : ({xP yP  : (Prod AP AP )}  → (*P xP yP ) ≡ (*P yP xP )) 
  
  record Hom (A1 A2  : Set ) (Ab1  : (AbelianGroup A1 )) (Ab2  : (AbelianGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-1 : (  (hom (1ᵢ Ab1 )  ) ≡ (1ᵢ Ab2 ) )
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ab1 ) x1 x2 ) ) ≡ ((* Ab2 ) (hom x1 ) (hom x2 ) ))
      pres-inv : ({x1  : A1}  → (hom ((inv Ab1 ) x1 ) ) ≡ ((inv Ab2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ab1  : (AbelianGroup A1 )) (Ab2  : (AbelianGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-1 : (  (interp (1ᵢ Ab1 )  (1ᵢ Ab2 )  ))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ab1 ) x1 x2 ) ((* Ab2 ) y1 y2 ) ))))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv Ab1 ) x1 ) ((inv Ab2 ) y1 ) ))) 
  
  data AbelianGroupTerm  : Set where
    1L : AbelianGroupTerm  
    *L : (AbelianGroupTerm   → (AbelianGroupTerm   → AbelianGroupTerm  ))
    invL : (AbelianGroupTerm   → AbelianGroupTerm  ) 
  
  data ClAbelianGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClAbelianGroupTerm A ) )
    1Cl : (ClAbelianGroupTerm A ) 
    *Cl : ((ClAbelianGroupTerm A )  → ((ClAbelianGroupTerm A )  → (ClAbelianGroupTerm A ) ))
    invCl : ((ClAbelianGroupTerm A )  → (ClAbelianGroupTerm A ) ) 
  
  data OpAbelianGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAbelianGroupTerm n ) )
    1OL : (OpAbelianGroupTerm n ) 
    *OL : ((OpAbelianGroupTerm n )  → ((OpAbelianGroupTerm n )  → (OpAbelianGroupTerm n ) ))
    invOL : ((OpAbelianGroupTerm n )  → (OpAbelianGroupTerm n ) ) 
  
  data OpAbelianGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAbelianGroupTerm2 n A ) )
    sing2 : (A  → (OpAbelianGroupTerm2 n A ) )
    1OL2 : (OpAbelianGroupTerm2 n A ) 
    *OL2 : ((OpAbelianGroupTerm2 n A )  → ((OpAbelianGroupTerm2 n A )  → (OpAbelianGroupTerm2 n A ) ))
    invOL2 : ((OpAbelianGroupTerm2 n A )  → (OpAbelianGroupTerm2 n A ) ) 
  
  simplifyB : (AbelianGroupTerm  → AbelianGroupTerm )
  simplifyB (*L 1L x )  = x 
  
  simplifyB (*L x 1L )  = x 
  
  simplifyB 1L  = 1L 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAbelianGroupTerm A ) → (ClAbelianGroupTerm A )))
  simplifyCl _ (*Cl 1Cl x )  = x 
  
  simplifyCl _ (*Cl x 1Cl )  = x 
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAbelianGroupTerm n ) → (OpAbelianGroupTerm n )))
  simplifyOp _ (*OL 1OL x )  = x 
  
  simplifyOp _ (*OL x 1OL )  = x 
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAbelianGroupTerm2 n A ) → (OpAbelianGroupTerm2 n A )))
  simplifyOpE _ _ (*OL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (*OL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AbelianGroup A ) → (AbelianGroupTerm  → A )))
  evalB Ab 1L  = (1ᵢ Ab ) 
  
  evalB Ab (*L x1 x2 )  = ((* Ab ) (evalB Ab x1 ) (evalB Ab x2 ) )
  
  evalB Ab (invL x1 )  = ((inv Ab ) (evalB Ab x1 ) )
  
  evalCl : ({A  : Set }  → ((AbelianGroup A ) → ((ClAbelianGroupTerm A ) → A )))
  evalCl Ab (sing x1 )  = x1 
  
  evalCl Ab 1Cl  = (1ᵢ Ab ) 
  
  evalCl Ab (*Cl x1 x2 )  = ((* Ab ) (evalCl Ab x1 ) (evalCl Ab x2 ) )
  
  evalCl Ab (invCl x1 )  = ((inv Ab ) (evalCl Ab x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AbelianGroup A ) → ((Vec A n ) → ((OpAbelianGroupTerm n ) → A ))))
  evalOp n Ab vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ab vars 1OL  = (1ᵢ Ab ) 
  
  evalOp n Ab vars (*OL x1 x2 )  = ((* Ab ) (evalOp n Ab vars x1 ) (evalOp n Ab vars x2 ) )
  
  evalOp n Ab vars (invOL x1 )  = ((inv Ab ) (evalOp n Ab vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AbelianGroup A ) → ((Vec A n ) → ((OpAbelianGroupTerm2 n A ) → A ))))
  evalOpE n Ab vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ab vars (sing2 x1 )  = x1 
  
  evalOpE n Ab vars 1OL2  = (1ᵢ Ab ) 
  
  evalOpE n Ab vars (*OL2 x1 x2 )  = ((* Ab ) (evalOpE n Ab vars x1 ) (evalOpE n Ab vars x2 ) )
  
  evalOpE n Ab vars (invOL2 x1 )  = ((inv Ab ) (evalOpE n Ab vars x1 ) )
  
  inductionB : ((P  : (AbelianGroupTerm  → Set ))  → ((P 1L ) → (((x1 x2  : AbelianGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1  : AbelianGroupTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((x  : AbelianGroupTerm )  → (P x ))))))
  inductionB p p1l p*l pinvl 1L  = p1l 
  
  inductionB p p1l p*l pinvl (*L x1 x2 )  = (p*l _ _ (inductionB p p1l p*l pinvl x1 ) (inductionB p p1l p*l pinvl x2 ) )
  
  inductionB p p1l p*l pinvl (invL x1 )  = (pinvl _ (inductionB p p1l p*l pinvl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAbelianGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 1Cl ) → (((x1 x2  : (ClAbelianGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1  : (ClAbelianGroupTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((x  : (ClAbelianGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing p1cl p*cl pinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p1cl p*cl pinvcl 1Cl  = p1cl 
  
  inductionCl _ p psing p1cl p*cl pinvcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p1cl p*cl pinvcl x1 ) (inductionCl _ p psing p1cl p*cl pinvcl x2 ) )
  
  inductionCl _ p psing p1cl p*cl pinvcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing p1cl p*cl pinvcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAbelianGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 1OL ) → (((x1 x2  : (OpAbelianGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1  : (OpAbelianGroupTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((x  : (OpAbelianGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv p1ol p*ol pinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p1ol p*ol pinvol 1OL  = p1ol 
  
  inductionOp _ p pv p1ol p*ol pinvol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p1ol p*ol pinvol x1 ) (inductionOp _ p pv p1ol p*ol pinvol x2 ) )
  
  inductionOp _ p pv p1ol p*ol pinvol (invOL x1 )  = (pinvol _ (inductionOp _ p pv p1ol p*ol pinvol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAbelianGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 1OL2 ) → (((x1 x2  : (OpAbelianGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1  : (OpAbelianGroupTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((x  : (OpAbelianGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 pinvol2 x1 ) )
  
  1L' : (  AbelianGroupTerm  )
  1L'  = 1L 
  
  *L' : (  (AbelianGroupTerm   → (AbelianGroupTerm   → AbelianGroupTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  invL' : (  (AbelianGroupTerm   → AbelianGroupTerm  ))
  invL' x1  = (invL x1 )
  
  stageB : (AbelianGroupTerm  → (Staged AbelianGroupTerm  ))
  stageB 1L  = (Now 1L )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  1Cl' : ({A  : Set }  → (ClAbelianGroupTerm A ) )
  1Cl'  = 1Cl 
  
  *Cl' : ({A  : Set }  → ((ClAbelianGroupTerm A )  → ((ClAbelianGroupTerm A )  → (ClAbelianGroupTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  invCl' : ({A  : Set }  → ((ClAbelianGroupTerm A )  → (ClAbelianGroupTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  stageCl : ((A  : Set )  → ((ClAbelianGroupTerm A ) → (Staged (ClAbelianGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  1OL' : ({n  : Nat}  → (OpAbelianGroupTerm n ) )
  1OL'  = 1OL 
  
  *OL' : ({n  : Nat}  → ((OpAbelianGroupTerm n )  → ((OpAbelianGroupTerm n )  → (OpAbelianGroupTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  invOL' : ({n  : Nat}  → ((OpAbelianGroupTerm n )  → (OpAbelianGroupTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpAbelianGroupTerm n ) → (Staged (OpAbelianGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpAbelianGroupTerm2 n A ) )
  1OL2'  = 1OL2 
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpAbelianGroupTerm2 n A )  → ((OpAbelianGroupTerm2 n A )  → (OpAbelianGroupTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpAbelianGroupTerm2 n A )  → (OpAbelianGroupTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAbelianGroupTerm2 n A ) → (Staged (OpAbelianGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      1T : (Repr A ) 
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      invT : ((Repr A )  → (Repr A ) ) 
   
