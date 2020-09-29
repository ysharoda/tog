
 module RingoidWithMultAntiDistrib  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RingoidWithMultAntiDistrib (A  : Set )  : Set where
    constructor RingoidWithMultAntiDistribC
    field
      * : (A  → (A  → A ))
      prim : (A  → A )
      antidis_prim_* : ({x y  : A }  → (prim (* x y ) ) ≡ (* (prim y ) (prim x ) ))
      + : (A  → (A  → A ))
      leftDistributive_*_+ : ({x y z  : A }  → (* x (+ y z ) ) ≡ (+ (* x y ) (* x z ) ))
      rightDistributive_*_+ : ({x y z  : A }  → (* (+ y z ) x ) ≡ (+ (* y x ) (* z x ) )) 
  
  open RingoidWithMultAntiDistrib
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      primS : (AS  → AS )
      +S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      primP : ((Prod AP AP ) → (Prod AP AP ))
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      antidis_prim_*P : ({xP yP  : (Prod AP AP )}  → (primP (*P xP yP ) ) ≡ (*P (primP yP ) (primP xP ) ))
      leftDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P xP (+P yP zP ) ) ≡ (+P (*P xP yP ) (*P xP zP ) ))
      rightDistributive_*_+P : ({xP yP zP  : (Prod AP AP )}  → (*P (+P yP zP ) xP ) ≡ (+P (*P yP xP ) (*P zP xP ) )) 
  
  record Hom (A1 A2  : Set ) (Ri1  : (RingoidWithMultAntiDistrib A1 )) (Ri2  : (RingoidWithMultAntiDistrib A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Ri1 ) x1 x2 ) ) ≡ ((* Ri2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim Ri1 ) x1 ) ) ≡ ((prim Ri2 ) (hom x1 ) ))
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Ri1 ) x1 x2 ) ) ≡ ((+ Ri2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ri1  : (RingoidWithMultAntiDistrib A1 )) (Ri2  : (RingoidWithMultAntiDistrib A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Ri1 ) x1 x2 ) ((* Ri2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Ri1 ) x1 ) ((prim Ri2 ) y1 ) )))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Ri1 ) x1 x2 ) ((+ Ri2 ) y1 y2 ) )))) 
  
  data RingoidWithMultAntiDistribTerm  : Set where
    *L : (RingoidWithMultAntiDistribTerm   → (RingoidWithMultAntiDistribTerm   → RingoidWithMultAntiDistribTerm  ))
    primL : (RingoidWithMultAntiDistribTerm   → RingoidWithMultAntiDistribTerm  )
    +L : (RingoidWithMultAntiDistribTerm   → (RingoidWithMultAntiDistribTerm   → RingoidWithMultAntiDistribTerm  )) 
  
  data ClRingoidWithMultAntiDistribTerm (A  : Set )  : Set where
    sing : (A  → (ClRingoidWithMultAntiDistribTerm A ) )
    *Cl : ((ClRingoidWithMultAntiDistribTerm A )  → ((ClRingoidWithMultAntiDistribTerm A )  → (ClRingoidWithMultAntiDistribTerm A ) ))
    primCl : ((ClRingoidWithMultAntiDistribTerm A )  → (ClRingoidWithMultAntiDistribTerm A ) )
    +Cl : ((ClRingoidWithMultAntiDistribTerm A )  → ((ClRingoidWithMultAntiDistribTerm A )  → (ClRingoidWithMultAntiDistribTerm A ) )) 
  
  data OpRingoidWithMultAntiDistribTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRingoidWithMultAntiDistribTerm n ) )
    *OL : ((OpRingoidWithMultAntiDistribTerm n )  → ((OpRingoidWithMultAntiDistribTerm n )  → (OpRingoidWithMultAntiDistribTerm n ) ))
    primOL : ((OpRingoidWithMultAntiDistribTerm n )  → (OpRingoidWithMultAntiDistribTerm n ) )
    +OL : ((OpRingoidWithMultAntiDistribTerm n )  → ((OpRingoidWithMultAntiDistribTerm n )  → (OpRingoidWithMultAntiDistribTerm n ) )) 
  
  data OpRingoidWithMultAntiDistribTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRingoidWithMultAntiDistribTerm2 n A ) )
    sing2 : (A  → (OpRingoidWithMultAntiDistribTerm2 n A ) )
    *OL2 : ((OpRingoidWithMultAntiDistribTerm2 n A )  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → (OpRingoidWithMultAntiDistribTerm2 n A ) ))
    primOL2 : ((OpRingoidWithMultAntiDistribTerm2 n A )  → (OpRingoidWithMultAntiDistribTerm2 n A ) )
    +OL2 : ((OpRingoidWithMultAntiDistribTerm2 n A )  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → (OpRingoidWithMultAntiDistribTerm2 n A ) )) 
  
  simplifyB : (RingoidWithMultAntiDistribTerm  → RingoidWithMultAntiDistribTerm )
  simplifyB (*L (primL y ) (primL x ) )  = (primL (*L x y ) )
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB (+L x1 x2 )  = (+L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRingoidWithMultAntiDistribTerm A ) → (ClRingoidWithMultAntiDistribTerm A )))
  simplifyCl _ (*Cl (primCl y ) (primCl x ) )  = (primCl (*Cl x y ) )
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (+Cl x1 x2 )  = (+Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRingoidWithMultAntiDistribTerm n ) → (OpRingoidWithMultAntiDistribTerm n )))
  simplifyOp _ (*OL (primOL y ) (primOL x ) )  = (primOL (*OL x y ) )
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (+OL x1 x2 )  = (+OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoidWithMultAntiDistribTerm2 n A ) → (OpRingoidWithMultAntiDistribTerm2 n A )))
  simplifyOpE _ _ (*OL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (*OL2 x y ) )
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (+OL2 x1 x2 )  = (+OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((RingoidWithMultAntiDistrib A ) → (RingoidWithMultAntiDistribTerm  → A )))
  evalB Ri (*L x1 x2 )  = ((* Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalB Ri (primL x1 )  = ((prim Ri ) (evalB Ri x1 ) )
  
  evalB Ri (+L x1 x2 )  = ((+ Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RingoidWithMultAntiDistrib A ) → ((ClRingoidWithMultAntiDistribTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (*Cl x1 x2 )  = ((* Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalCl Ri (primCl x1 )  = ((prim Ri ) (evalCl Ri x1 ) )
  
  evalCl Ri (+Cl x1 x2 )  = ((+ Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RingoidWithMultAntiDistrib A ) → ((Vec A n ) → ((OpRingoidWithMultAntiDistribTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (*OL x1 x2 )  = ((* Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOp n Ri vars (primOL x1 )  = ((prim Ri ) (evalOp n Ri vars x1 ) )
  
  evalOp n Ri vars (+OL x1 x2 )  = ((+ Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RingoidWithMultAntiDistrib A ) → ((Vec A n ) → ((OpRingoidWithMultAntiDistribTerm2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (*OL2 x1 x2 )  = ((* Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  evalOpE n Ri vars (primOL2 x1 )  = ((prim Ri ) (evalOpE n Ri vars x1 ) )
  
  evalOpE n Ri vars (+OL2 x1 x2 )  = ((+ Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RingoidWithMultAntiDistribTerm  → Set ))  → (((x1 x2  : RingoidWithMultAntiDistribTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1  : RingoidWithMultAntiDistribTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : RingoidWithMultAntiDistribTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : RingoidWithMultAntiDistribTerm )  → (P x ))))))
  inductionB p p*l ppriml p+l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l ppriml p+l x1 ) (inductionB p p*l ppriml p+l x2 ) )
  
  inductionB p p*l ppriml p+l (primL x1 )  = (ppriml _ (inductionB p p*l ppriml p+l x1 ) )
  
  inductionB p p*l ppriml p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p*l ppriml p+l x1 ) (inductionB p p*l ppriml p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRingoidWithMultAntiDistribTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRingoidWithMultAntiDistribTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1  : (ClRingoidWithMultAntiDistribTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClRingoidWithMultAntiDistribTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClRingoidWithMultAntiDistribTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl pprimcl p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl pprimcl p+cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl pprimcl p+cl x1 ) (inductionCl _ p psing p*cl pprimcl p+cl x2 ) )
  
  inductionCl _ p psing p*cl pprimcl p+cl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl pprimcl p+cl x1 ) )
  
  inductionCl _ p psing p*cl pprimcl p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p*cl pprimcl p+cl x1 ) (inductionCl _ p psing p*cl pprimcl p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRingoidWithMultAntiDistribTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRingoidWithMultAntiDistribTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1  : (OpRingoidWithMultAntiDistribTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpRingoidWithMultAntiDistribTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpRingoidWithMultAntiDistribTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol pprimol p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol pprimol p+ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol pprimol p+ol x1 ) (inductionOp _ p pv p*ol pprimol p+ol x2 ) )
  
  inductionOp _ p pv p*ol pprimol p+ol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol pprimol p+ol x1 ) )
  
  inductionOp _ p pv p*ol pprimol p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p*ol pprimol p+ol x1 ) (inductionOp _ p pv p*ol pprimol p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRingoidWithMultAntiDistribTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRingoidWithMultAntiDistribTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1  : (OpRingoidWithMultAntiDistribTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpRingoidWithMultAntiDistribTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpRingoidWithMultAntiDistribTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p+ol2 x2 ) )
  
  *L' : (  (RingoidWithMultAntiDistribTerm   → (RingoidWithMultAntiDistribTerm   → RingoidWithMultAntiDistribTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  primL' : (  (RingoidWithMultAntiDistribTerm   → RingoidWithMultAntiDistribTerm  ))
  primL' x1  = (primL x1 )
  
  +L' : (  (RingoidWithMultAntiDistribTerm   → (RingoidWithMultAntiDistribTerm   → RingoidWithMultAntiDistribTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (RingoidWithMultAntiDistribTerm  → (Staged RingoidWithMultAntiDistribTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  *Cl' : ({A  : Set }  → ((ClRingoidWithMultAntiDistribTerm A )  → ((ClRingoidWithMultAntiDistribTerm A )  → (ClRingoidWithMultAntiDistribTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClRingoidWithMultAntiDistribTerm A )  → (ClRingoidWithMultAntiDistribTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  +Cl' : ({A  : Set }  → ((ClRingoidWithMultAntiDistribTerm A )  → ((ClRingoidWithMultAntiDistribTerm A )  → (ClRingoidWithMultAntiDistribTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRingoidWithMultAntiDistribTerm A ) → (Staged (ClRingoidWithMultAntiDistribTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  *OL' : ({n  : Nat}  → ((OpRingoidWithMultAntiDistribTerm n )  → ((OpRingoidWithMultAntiDistribTerm n )  → (OpRingoidWithMultAntiDistribTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpRingoidWithMultAntiDistribTerm n )  → (OpRingoidWithMultAntiDistribTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  +OL' : ({n  : Nat}  → ((OpRingoidWithMultAntiDistribTerm n )  → ((OpRingoidWithMultAntiDistribTerm n )  → (OpRingoidWithMultAntiDistribTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRingoidWithMultAntiDistribTerm n ) → (Staged (OpRingoidWithMultAntiDistribTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → (OpRingoidWithMultAntiDistribTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → (OpRingoidWithMultAntiDistribTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → ((OpRingoidWithMultAntiDistribTerm2 n A )  → (OpRingoidWithMultAntiDistribTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRingoidWithMultAntiDistribTerm2 n A ) → (Staged (OpRingoidWithMultAntiDistribTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      primT : ((Repr A )  → (Repr A ) )
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
