
 module PointedInvolutiveMagma0Sig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointedInvolutiveMagma0Sig (A  : Set ) (*  : (A  → (A  → A ))) (prim  : (A  → A )) (0ᵢ  : A )  : Set where
    constructor IsPointedInvolutiveMagma0SigC
   
  
  record PointedInvolutiveMagma0Sig (A  : Set )  : Set where
    constructor PointedInvolutiveMagma0SigC
    field
      * : (A  → (A  → A ))
      prim : (A  → A )
      0ᵢ : A 
      isPointedInvolutiveMagma0Sig : (IsPointedInvolutiveMagma0Sig A (*) prim 0ᵢ ) 
  
  open PointedInvolutiveMagma0Sig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      primS : (AS  → AS )
      0S : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      primP : ((Prod AP AP ) → (Prod AP AP ))
      0P : (Prod AP AP ) 
  
  record Hom (A1 A2  : Set ) (Po1  : (PointedInvolutiveMagma0Sig A1 )) (Po2  : (PointedInvolutiveMagma0Sig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Po1 ) x1 x2 ) ) ≡ ((* Po2 ) (hom x1 ) (hom x2 ) ))
      pres-prim : ({x1  : A1}  → (hom ((prim Po1 ) x1 ) ) ≡ ((prim Po2 ) (hom x1 ) ))
      pres-0 : (  (hom (0ᵢ Po1 )  ) ≡ (0ᵢ Po2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Po1  : (PointedInvolutiveMagma0Sig A1 )) (Po2  : (PointedInvolutiveMagma0Sig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Po1 ) x1 x2 ) ((* Po2 ) y1 y2 ) ))))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Po1 ) x1 ) ((prim Po2 ) y1 ) )))
      interp-0 : (  (interp (0ᵢ Po1 )  (0ᵢ Po2 )  )) 
  
  data PointedInvolutiveMagma0SigTerm  : Set where
    *L : (PointedInvolutiveMagma0SigTerm   → (PointedInvolutiveMagma0SigTerm   → PointedInvolutiveMagma0SigTerm  ))
    primL : (PointedInvolutiveMagma0SigTerm   → PointedInvolutiveMagma0SigTerm  )
    0L : PointedInvolutiveMagma0SigTerm   
  
  data ClPointedInvolutiveMagma0SigTerm (A  : Set )  : Set where
    sing : (A  → (ClPointedInvolutiveMagma0SigTerm A ) )
    *Cl : ((ClPointedInvolutiveMagma0SigTerm A )  → ((ClPointedInvolutiveMagma0SigTerm A )  → (ClPointedInvolutiveMagma0SigTerm A ) ))
    primCl : ((ClPointedInvolutiveMagma0SigTerm A )  → (ClPointedInvolutiveMagma0SigTerm A ) )
    0Cl : (ClPointedInvolutiveMagma0SigTerm A )  
  
  data OpPointedInvolutiveMagma0SigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointedInvolutiveMagma0SigTerm n ) )
    *OL : ((OpPointedInvolutiveMagma0SigTerm n )  → ((OpPointedInvolutiveMagma0SigTerm n )  → (OpPointedInvolutiveMagma0SigTerm n ) ))
    primOL : ((OpPointedInvolutiveMagma0SigTerm n )  → (OpPointedInvolutiveMagma0SigTerm n ) )
    0OL : (OpPointedInvolutiveMagma0SigTerm n )  
  
  data OpPointedInvolutiveMagma0SigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointedInvolutiveMagma0SigTerm2 n A ) )
    sing2 : (A  → (OpPointedInvolutiveMagma0SigTerm2 n A ) )
    *OL2 : ((OpPointedInvolutiveMagma0SigTerm2 n A )  → ((OpPointedInvolutiveMagma0SigTerm2 n A )  → (OpPointedInvolutiveMagma0SigTerm2 n A ) ))
    primOL2 : ((OpPointedInvolutiveMagma0SigTerm2 n A )  → (OpPointedInvolutiveMagma0SigTerm2 n A ) )
    0OL2 : (OpPointedInvolutiveMagma0SigTerm2 n A )  
  
  simplifyB : (PointedInvolutiveMagma0SigTerm  → PointedInvolutiveMagma0SigTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB 0L  = 0L 
  
  simplifyCl : ((A  : Set )  → ((ClPointedInvolutiveMagma0SigTerm A ) → (ClPointedInvolutiveMagma0SigTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPointedInvolutiveMagma0SigTerm n ) → (OpPointedInvolutiveMagma0SigTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedInvolutiveMagma0SigTerm2 n A ) → (OpPointedInvolutiveMagma0SigTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PointedInvolutiveMagma0Sig A ) → (PointedInvolutiveMagma0SigTerm  → A )))
  evalB Po (*L x1 x2 )  = ((* Po ) (evalB Po x1 ) (evalB Po x2 ) )
  
  evalB Po (primL x1 )  = ((prim Po ) (evalB Po x1 ) )
  
  evalB Po 0L  = (0ᵢ Po ) 
  
  evalCl : ({A  : Set }  → ((PointedInvolutiveMagma0Sig A ) → ((ClPointedInvolutiveMagma0SigTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po (*Cl x1 x2 )  = ((* Po ) (evalCl Po x1 ) (evalCl Po x2 ) )
  
  evalCl Po (primCl x1 )  = ((prim Po ) (evalCl Po x1 ) )
  
  evalCl Po 0Cl  = (0ᵢ Po ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PointedInvolutiveMagma0Sig A ) → ((Vec A n ) → ((OpPointedInvolutiveMagma0SigTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars (*OL x1 x2 )  = ((* Po ) (evalOp n Po vars x1 ) (evalOp n Po vars x2 ) )
  
  evalOp n Po vars (primOL x1 )  = ((prim Po ) (evalOp n Po vars x1 ) )
  
  evalOp n Po vars 0OL  = (0ᵢ Po ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PointedInvolutiveMagma0Sig A ) → ((Vec A n ) → ((OpPointedInvolutiveMagma0SigTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars (*OL2 x1 x2 )  = ((* Po ) (evalOpE n Po vars x1 ) (evalOpE n Po vars x2 ) )
  
  evalOpE n Po vars (primOL2 x1 )  = ((prim Po ) (evalOpE n Po vars x1 ) )
  
  evalOpE n Po vars 0OL2  = (0ᵢ Po ) 
  
  inductionB : ((P  : (PointedInvolutiveMagma0SigTerm  → Set ))  → (((x1 x2  : PointedInvolutiveMagma0SigTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → (((x1  : PointedInvolutiveMagma0SigTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → ((P 0L ) → ((x  : PointedInvolutiveMagma0SigTerm )  → (P x ))))))
  inductionB p p*l ppriml p0l (*L x1 x2 )  = (p*l _ _ (inductionB p p*l ppriml p0l x1 ) (inductionB p p*l ppriml p0l x2 ) )
  
  inductionB p p*l ppriml p0l (primL x1 )  = (ppriml _ (inductionB p p*l ppriml p0l x1 ) )
  
  inductionB p p*l ppriml p0l 0L  = p0l 
  
  inductionCl : ((A  : Set ) (P  : ((ClPointedInvolutiveMagma0SigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClPointedInvolutiveMagma0SigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → (((x1  : (ClPointedInvolutiveMagma0SigTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → ((P 0Cl ) → ((x  : (ClPointedInvolutiveMagma0SigTerm A ))  → (P x )))))))
  inductionCl _ p psing p*cl pprimcl p0cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl pprimcl p0cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl pprimcl p0cl x1 ) (inductionCl _ p psing p*cl pprimcl p0cl x2 ) )
  
  inductionCl _ p psing p*cl pprimcl p0cl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing p*cl pprimcl p0cl x1 ) )
  
  inductionCl _ p psing p*cl pprimcl p0cl 0Cl  = p0cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpPointedInvolutiveMagma0SigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpPointedInvolutiveMagma0SigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → (((x1  : (OpPointedInvolutiveMagma0SigTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → ((P 0OL ) → ((x  : (OpPointedInvolutiveMagma0SigTerm n ))  → (P x )))))))
  inductionOp _ p pv p*ol pprimol p0ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol pprimol p0ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol pprimol p0ol x1 ) (inductionOp _ p pv p*ol pprimol p0ol x2 ) )
  
  inductionOp _ p pv p*ol pprimol p0ol (primOL x1 )  = (pprimol _ (inductionOp _ p pv p*ol pprimol p0ol x1 ) )
  
  inductionOp _ p pv p*ol pprimol p0ol 0OL  = p0ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointedInvolutiveMagma0SigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpPointedInvolutiveMagma0SigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → (((x1  : (OpPointedInvolutiveMagma0SigTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → ((P 0OL2 ) → ((x  : (OpPointedInvolutiveMagma0SigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 pprimol2 p0ol2 0OL2  = p0ol2 
  
  *L' : (  (PointedInvolutiveMagma0SigTerm   → (PointedInvolutiveMagma0SigTerm   → PointedInvolutiveMagma0SigTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  primL' : (  (PointedInvolutiveMagma0SigTerm   → PointedInvolutiveMagma0SigTerm  ))
  primL' x1  = (primL x1 )
  
  0L' : (  PointedInvolutiveMagma0SigTerm  )
  0L'  = 0L 
  
  stageB : (PointedInvolutiveMagma0SigTerm  → (Staged PointedInvolutiveMagma0SigTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB 0L  = (Now 0L )
  
  *Cl' : ({A  : Set }  → ((ClPointedInvolutiveMagma0SigTerm A )  → ((ClPointedInvolutiveMagma0SigTerm A )  → (ClPointedInvolutiveMagma0SigTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  primCl' : ({A  : Set }  → ((ClPointedInvolutiveMagma0SigTerm A )  → (ClPointedInvolutiveMagma0SigTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  0Cl' : ({A  : Set }  → (ClPointedInvolutiveMagma0SigTerm A ) )
  0Cl'  = 0Cl 
  
  stageCl : ((A  : Set )  → ((ClPointedInvolutiveMagma0SigTerm A ) → (Staged (ClPointedInvolutiveMagma0SigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  *OL' : ({n  : Nat}  → ((OpPointedInvolutiveMagma0SigTerm n )  → ((OpPointedInvolutiveMagma0SigTerm n )  → (OpPointedInvolutiveMagma0SigTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  primOL' : ({n  : Nat}  → ((OpPointedInvolutiveMagma0SigTerm n )  → (OpPointedInvolutiveMagma0SigTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  0OL' : ({n  : Nat}  → (OpPointedInvolutiveMagma0SigTerm n ) )
  0OL'  = 0OL 
  
  stageOp : ((n  : Nat)  → ((OpPointedInvolutiveMagma0SigTerm n ) → (Staged (OpPointedInvolutiveMagma0SigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpPointedInvolutiveMagma0SigTerm2 n A )  → ((OpPointedInvolutiveMagma0SigTerm2 n A )  → (OpPointedInvolutiveMagma0SigTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpPointedInvolutiveMagma0SigTerm2 n A )  → (OpPointedInvolutiveMagma0SigTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpPointedInvolutiveMagma0SigTerm2 n A ) )
  0OL2'  = 0OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedInvolutiveMagma0SigTerm2 n A ) → (Staged (OpPointedInvolutiveMagma0SigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      primT : ((Repr A )  → (Repr A ) )
      0T : (Repr A )  
   
