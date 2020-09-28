module DualDeMorgan  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record DualDeMorgan (A  : Set )  : Set where
    constructor DualDeMorganC
    field
      * : (A  → (A  → A ))
      + : (A  → (A  → A ))
      prim : (A  → A )
      andDeMorgan_*_+_prim : ({x y z  : A }  → (prim (* x y ) ) ≡ (+ (prim x ) (prim y ) ))
      orDeMorgan_+_*_prim : ({x y z  : A }  → (prim (+ x y ) ) ≡ (* (prim x ) (prim y ) ))
  open DualDeMorgan
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
      andDeMorgan_*_+_primP : ({xP yP zP  : (Prod AP AP )}  → (primP (*P xP yP ) ) ≡ (+P (primP xP ) (primP yP ) ))
      orDeMorgan_+_*_primP : ({xP yP zP  : (Prod AP AP )}  → (primP (+P xP yP ) ) ≡ (*P (primP xP ) (primP yP ) ))
  record Hom (A1 A2  : Set ) (Du1  : (DualDeMorgan A1 )) (Du2  : (DualDeMorgan A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Du1 ) x1 x2 ) ) ≡ ((* Du2 ) (hom x1 ) (hom x2 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Du1 ) x1 x2 ) ) ≡ ((+ Du2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim Du1 ) x1 ) ) ≡ ((prim Du2 ) (hom x1 ) ))
  record RelInterp (A1 A2  : Set ) (Du1  : (DualDeMorgan A1 )) (Du2  : (DualDeMorgan A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Du1 ) x1 x2 ) ((* Du2 ) y1 y2 ) ))))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Du1 ) x1 x2 ) ((+ Du2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Du1 ) x1 ) ((prim Du2 ) y1 ) )))
  data DualDeMorganTerm  : Set where
    *L : (DualDeMorganTerm   → (DualDeMorganTerm   → DualDeMorganTerm  ))
    +L : (DualDeMorganTerm   → (DualDeMorganTerm   → DualDeMorganTerm  ))
    primL : (DualDeMorganTerm   → DualDeMorganTerm  )
  data ClDualDeMorganTerm (A  : Set )  : Set where
    sing : (A  → (ClDualDeMorganTerm A ) )
    *Cl : ((ClDualDeMorganTerm A )  → ((ClDualDeMorganTerm A )  → (ClDualDeMorganTerm A ) ))
    +Cl : ((ClDualDeMorganTerm A )  → ((ClDualDeMorganTerm A )  → (ClDualDeMorganTerm A ) ))
    primCl : ((ClDualDeMorganTerm A )  → (ClDualDeMorganTerm A ) )
  data OpDualDeMorganTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpDualDeMorganTerm n ) )
    *OL : ((OpDualDeMorganTerm n )  → ((OpDualDeMorganTerm n )  → (OpDualDeMorganTerm n ) ))
    +OL : ((OpDualDeMorganTerm n )  → ((OpDualDeMorganTerm n )  → (OpDualDeMorganTerm n ) ))
    primOL : ((OpDualDeMorganTerm n )  → (OpDualDeMorganTerm n ) )
  data OpDualDeMorganTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpDualDeMorganTerm2 n A ) )
    sing2 : (A  → (OpDualDeMorganTerm2 n A ) )
    *OL2 : ((OpDualDeMorganTerm2 n A )  → ((OpDualDeMorganTerm2 n A )  → (OpDualDeMorganTerm2 n A ) ))
    +OL2 : ((OpDualDeMorganTerm2 n A )  → ((OpDualDeMorganTerm2 n A )  → (OpDualDeMorganTerm2 n A ) ))
    primOL2 : ((OpDualDeMorganTerm2 n A )  → (OpDualDeMorganTerm2 n A ) )
  evalB : ({A  : Set }  → ((DualDeMorgan A ) → (DualDeMorganTerm  → A )))
  evalB Du (*L x1 x2 )  = ((* Du ) (evalB Du x1 ) (evalB Du x2 ) )
  
  evalB Du (+L x1 x2 )  = ((+ Du ) (evalB Du x1 ) (evalB Du x2 ) )
  
  evalB Du (primL x1 )  = ((prim Du ) (evalB Du x1 ) )
  
  evalCl : ({A  : Set }  → ((DualDeMorgan A ) → ((ClDualDeMorganTerm A ) → A )))
  evalCl Du (sing x1 )  = x1 
  
  evalCl Du (*Cl x1 x2 )  = ((* Du ) (evalCl Du x1 ) (evalCl Du x2 ) )
  
  evalCl Du (+Cl x1 x2 )  = ((+ Du ) (evalCl Du x1 ) (evalCl Du x2 ) )
  
  evalCl Du (primCl x1 )  = ((prim Du ) (evalCl Du x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((DualDeMorgan A ) → ((Vec A n ) → ((OpDualDeMorganTerm n ) → A ))))
  evalOp n Du vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Du vars (*OL x1 x2 )  = ((* Du ) (evalOp n Du vars x1 ) (evalOp n Du vars x2 ) )
  
  evalOp n Du vars (+OL x1 x2 )  = ((+ Du ) (evalOp n Du vars x1 ) (evalOp n Du vars x2 ) )
  
  evalOp n Du vars (primOL x1 )  = ((prim Du ) (evalOp n Du vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((DualDeMorgan A ) → ((Vec A n ) → ((OpDualDeMorganTerm2 n A ) → A ))))
  evalOpE n Du vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Du vars (sing2 x1 )  = x1 
  
  evalOpE n Du vars (*OL2 x1 x2 )  = ((* Du ) (evalOpE n Du vars x1 ) (evalOpE n Du vars x2 ) )
  
  evalOpE n Du vars (+OL2 x1 x2 )  = ((+ Du ) (evalOpE n Du vars x1 ) (evalOpE n Du vars x2 ) )
  
  evalOpE n Du vars (primOL2 x1 )  = ((prim Du ) (evalOpE n Du vars x1 ) )
  
  inductionB : ((P  : (DualDeMorganTerm  → Set ))  → (((x1 x2  : DualDeMorganTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1 x2  : DualDeMorganTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → (((x1  : DualDeMorganTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((x  : DualDeMorganTerm )  → (P x ))))))
  inductionB p p*l p+l ppriml (*L x1 x2 )  = (p*l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (+L x1 x2 )  = (p+l _ _ (inductionB p p*l p+l ppriml x1 ) (inductionB p p*l p+l ppriml x2 ) )
  
  inductionB p p*l p+l ppriml (primL x1 )  = (ppriml _ (inductionB p p*l p+l ppriml x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClDualDeMorganTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClDualDeMorganTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1 x2  : (ClDualDeMorganTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → (((x1  : (ClDualDeMorganTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((x  : (ClDualDeMorganTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl p+cl pprimcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl p+cl pprimcl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) (inductionCl _ p psing p*cl p+cl pprimcl x2 ) )
  
  inductionCl _ p psing p*cl p+cl pprimcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl p+cl pprimcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpDualDeMorganTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpDualDeMorganTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1 x2  : (OpDualDeMorganTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → (((x1  : (OpDualDeMorganTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((x  : (OpDualDeMorganTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol p+ol pprimol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol p+ol pprimol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) (inductionOp _ p pv p*ol p+ol pprimol x2 ) )
  
  inductionOp _ p pv p*ol p+ol pprimol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol p+ol pprimol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpDualDeMorganTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpDualDeMorganTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1 x2  : (OpDualDeMorganTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → (((x1  : (OpDualDeMorganTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((x  : (OpDualDeMorganTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 p+ol2 pprimol2 x1 ) )
  
  *L' : (  (DualDeMorganTerm   → (DualDeMorganTerm   → DualDeMorganTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  +L' : (  (DualDeMorganTerm   → (DualDeMorganTerm   → DualDeMorganTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  primL' : (  (DualDeMorganTerm   → DualDeMorganTerm  ))
  primL' x1  = (primL x1 )
  
  stageB : (DualDeMorganTerm  → (Staged DualDeMorganTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  *Cl' : ({A  : Set }  → ((ClDualDeMorganTerm A )  → ((ClDualDeMorganTerm A )  → (ClDualDeMorganTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  +Cl' : ({A  : Set }  → ((ClDualDeMorganTerm A )  → ((ClDualDeMorganTerm A )  → (ClDualDeMorganTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClDualDeMorganTerm A )  → (ClDualDeMorganTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  stageCl : ((A  : Set )  → ((ClDualDeMorganTerm A ) → (Staged (ClDualDeMorganTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  *OL' : ({n  : Nat}  → ((OpDualDeMorganTerm n )  → ((OpDualDeMorganTerm n )  → (OpDualDeMorganTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  +OL' : ({n  : Nat}  → ((OpDualDeMorganTerm n )  → ((OpDualDeMorganTerm n )  → (OpDualDeMorganTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpDualDeMorganTerm n )  → (OpDualDeMorganTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpDualDeMorganTerm n ) → (Staged (OpDualDeMorganTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpDualDeMorganTerm2 n A )  → ((OpDualDeMorganTerm2 n A )  → (OpDualDeMorganTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpDualDeMorganTerm2 n A )  → ((OpDualDeMorganTerm2 n A )  → (OpDualDeMorganTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpDualDeMorganTerm2 n A )  → (OpDualDeMorganTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpDualDeMorganTerm2 n A ) → (Staged (OpDualDeMorganTerm2 n A ) )))
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