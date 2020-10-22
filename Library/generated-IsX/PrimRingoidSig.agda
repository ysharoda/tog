
 module PrimRingoidSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPrimRingoidSig (A  : Set ) (*  : (A  → (A  → A ))) (+  : (A  → (A  → A ))) (prim  : (A  → A ))  : Set where
    constructor IsPrimRingoidSigC
   
  
  record PrimRingoidSig (A  : Set )  : Set where
    constructor PrimRingoidSigC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      prim : (A  → A )
      isPrimRingoidSig : (IsPrimRingoidSig A (*) (+) prim ) 
  
  open PrimRingoidSig
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
  
  record Hom (A1 A2  : Set ) (Pr1  : (PrimRingoidSig A1 )) (Pr2  : (PrimRingoidSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Pr1 ) x1 x2 ) ) ≡ ((* Pr2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Pr1 ) x1 x2 ) ) ≡ ((+ Pr2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim Pr1 ) x1 ) ) ≡ ((prim Pr2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Pr1  : (PrimRingoidSig A1 )) (Pr2  : (PrimRingoidSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Pr1 ) x1 x2 ) ((* Pr2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Pr1 ) x1 x2 ) ((+ Pr2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Pr1 ) x1 ) ((prim Pr2 ) y1 ) ))) 
  
  data PrimRingoidSigTerm  : Set where
    *L : (PrimRingoidSigTerm   → (PrimRingoidSigTerm   → PrimRingoidSigTerm  ))
    +L : (PrimRingoidSigTerm   → (PrimRingoidSigTerm   → PrimRingoidSigTerm  ))
    primL : (PrimRingoidSigTerm   → PrimRingoidSigTerm  ) 
  
  data ClPrimRingoidSigTerm (A  : Set )  : Set where
    sing : (A  → (ClPrimRingoidSigTerm A ) )
    *Cl : ((ClPrimRingoidSigTerm A )  → ((ClPrimRingoidSigTerm A )  → (ClPrimRingoidSigTerm A ) ))
    +Cl : ((ClPrimRingoidSigTerm A )  → ((ClPrimRingoidSigTerm A )  → (ClPrimRingoidSigTerm A ) ))
    primCl : ((ClPrimRingoidSigTerm A )  → (ClPrimRingoidSigTerm A ) ) 
  
  data OpPrimRingoidSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPrimRingoidSigTerm n ) )
    *OL : ((OpPrimRingoidSigTerm n )  → ((OpPrimRingoidSigTerm n )  → (OpPrimRingoidSigTerm n ) ))
    +OL : ((OpPrimRingoidSigTerm n )  → ((OpPrimRingoidSigTerm n )  → (OpPrimRingoidSigTerm n ) ))
    primOL : ((OpPrimRingoidSigTerm n )  → (OpPrimRingoidSigTerm n ) ) 
  
  data OpPrimRingoidSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPrimRingoidSigTerm2 n A ) )
    sing2 : (A  → (OpPrimRingoidSigTerm2 n A ) )
    *OL2 : ((OpPrimRingoidSigTerm2 n A )  → ((OpPrimRingoidSigTerm2 n A )  → (OpPrimRingoidSigTerm2 n A ) ))
    +OL2 : ((OpPrimRingoidSigTerm2 n A )  → ((OpPrimRingoidSigTerm2 n A )  → (OpPrimRingoidSigTerm2 n A ) ))
    primOL2 : ((OpPrimRingoidSigTerm2 n A )  → (OpPrimRingoidSigTerm2 n A ) ) 
  
  simplifyB : (PrimRingoidSigTerm  → PrimRingoidSigTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClPrimRingoidSigTerm A ) → (ClPrimRingoidSigTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPrimRingoidSigTerm n ) → (OpPrimRingoidSigTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPrimRingoidSigTerm2 n A ) → (OpPrimRingoidSigTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PrimRingoidSig A ) → (PrimRingoidSigTerm  → A )))
  evalB Pr (*L x1 x2 )  = ((* Pr ) (evalB Pr x1 ) (evalB Pr x2 ) )
  
  evalB Pr (+L x1 x2 )  = ((+ Pr ) (evalB Pr x1 ) (evalB Pr x2 ) )
  
  evalB Pr (primL x1 )  = ((prim Pr ) (evalB Pr x1 ) )
  
  evalCl : ({A  : Set }  → ((PrimRingoidSig A ) → ((ClPrimRingoidSigTerm A ) → A )))
  evalCl Pr (sing x1 )  = x1 
  
  evalCl Pr (*Cl x1 x2 )  = ((* Pr ) (evalCl Pr x1 ) (evalCl Pr x2 ) )
  
  evalCl Pr (+Cl x1 x2 )  = ((+ Pr ) (evalCl Pr x1 ) (evalCl Pr x2 ) )
  
  evalCl Pr (primCl x1 )  = ((prim Pr ) (evalCl Pr x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PrimRingoidSig A ) → ((Vec A n ) → ((OpPrimRingoidSigTerm n ) → A ))))
  evalOp n Pr vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Pr vars (*OL x1 x2 )  = ((* Pr ) (evalOp n Pr vars x1 ) (evalOp n Pr vars x2 ) )
  
  evalOp n Pr vars (+OL x1 x2 )  = ((+ Pr ) (evalOp n Pr vars x1 ) (evalOp n Pr vars x2 ) )
  
  evalOp n Pr vars (primOL x1 )  = ((prim Pr ) (evalOp n Pr vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PrimRingoidSig A ) → ((Vec A n ) → ((OpPrimRingoidSigTerm2 n A ) → A ))))
  evalOpE n Pr vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Pr vars (sing2 x1 )  = x1 
  
  evalOpE n Pr vars (*OL2 x1 x2 )  = ((* Pr ) (evalOpE n Pr vars x1 ) (evalOpE n Pr vars x2 ) )
  
  evalOpE n Pr vars (+OL2 x1 x2 )  = ((+ Pr ) (evalOpE n Pr vars x1 ) (evalOpE n Pr vars x2 ) )
  
  evalOpE n Pr vars (primOL2 x1 )  = ((prim Pr ) (evalOpE n Pr vars x1 ) )
  
  inductionB : ((P  : (PrimRingoidSigTerm  → Set ))  → (((x1 x2  : PrimRingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : PrimRingoidSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1  : PrimRingoidSigTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : PrimRingoidSigTerm )  → (P x ))))))
  inductionB p p*l p+l ppriml (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (primL x1 )  = (ppriml _ (inductionB p p*l p+l ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClPrimRingoidSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClPrimRingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClPrimRingoidSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1  : (ClPrimRingoidSigTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClPrimRingoidSigTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p+cl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl pprimcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpPrimRingoidSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpPrimRingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpPrimRingoidSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1  : (OpPrimRingoidSigTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpPrimRingoidSigTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p+ol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol pprimol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPrimRingoidSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpPrimRingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpPrimRingoidSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1  : (OpPrimRingoidSigTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpPrimRingoidSigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) )
  
  *L' : (  (PrimRingoidSigTerm   → (PrimRingoidSigTerm   → PrimRingoidSigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (PrimRingoidSigTerm   → (PrimRingoidSigTerm   → PrimRingoidSigTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  primL' : (  (PrimRingoidSigTerm   → PrimRingoidSigTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (PrimRingoidSigTerm  → (Staged PrimRingoidSigTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  *Cl' : ({A  : Set }  → ((ClPrimRingoidSigTerm A )  → ((ClPrimRingoidSigTerm A )  → (ClPrimRingoidSigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClPrimRingoidSigTerm A )  → ((ClPrimRingoidSigTerm A )  → (ClPrimRingoidSigTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClPrimRingoidSigTerm A )  → (ClPrimRingoidSigTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClPrimRingoidSigTerm A ) → (Staged (ClPrimRingoidSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  *OL' : ({n  : Nat}  → ((OpPrimRingoidSigTerm n )  → ((OpPrimRingoidSigTerm n )  → (OpPrimRingoidSigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpPrimRingoidSigTerm n )  → ((OpPrimRingoidSigTerm n )  → (OpPrimRingoidSigTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpPrimRingoidSigTerm n )  → (OpPrimRingoidSigTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpPrimRingoidSigTerm n ) → (Staged (OpPrimRingoidSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpPrimRingoidSigTerm2 n A )  → ((OpPrimRingoidSigTerm2 n A )  → (OpPrimRingoidSigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpPrimRingoidSigTerm2 n A )  → ((OpPrimRingoidSigTerm2 n A )  → (OpPrimRingoidSigTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpPrimRingoidSigTerm2 n A )  → (OpPrimRingoidSigTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPrimRingoidSigTerm2 n A ) → (Staged (OpPrimRingoidSigTerm2 n A ) )))
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
   
