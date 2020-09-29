
 module PointedTimesZeroMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record PointedTimesZeroMagma (A  : Set )  : Set where
    constructor PointedTimesZeroMagmaC
    field
      0ᵢ : A 
      * : (A  → (A  → A )) 
  
  open PointedTimesZeroMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS 
      *S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP )
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (Po1  : (PointedTimesZeroMagma A1 )) (Po2  : (PointedTimesZeroMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Po1 )  ) ≡ (0ᵢ Po2 ) )
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Po1 ) x1 x2 ) ) ≡ ((* Po2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Po1  : (PointedTimesZeroMagma A1 )) (Po2  : (PointedTimesZeroMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Po1 )  (0ᵢ Po2 )  ))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Po1 ) x1 x2 ) ((* Po2 ) y1 y2 ) )))) 
  
  data PointedTimesZeroMagmaTerm  : Set where
    0L : PointedTimesZeroMagmaTerm  
    *L : (PointedTimesZeroMagmaTerm   → (PointedTimesZeroMagmaTerm   → PointedTimesZeroMagmaTerm  )) 
  
  data ClPointedTimesZeroMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClPointedTimesZeroMagmaTerm A ) )
    0Cl : (ClPointedTimesZeroMagmaTerm A ) 
    *Cl : ((ClPointedTimesZeroMagmaTerm A )  → ((ClPointedTimesZeroMagmaTerm A )  → (ClPointedTimesZeroMagmaTerm A ) )) 
  
  data OpPointedTimesZeroMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointedTimesZeroMagmaTerm n ) )
    0OL : (OpPointedTimesZeroMagmaTerm n ) 
    *OL : ((OpPointedTimesZeroMagmaTerm n )  → ((OpPointedTimesZeroMagmaTerm n )  → (OpPointedTimesZeroMagmaTerm n ) )) 
  
  data OpPointedTimesZeroMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointedTimesZeroMagmaTerm2 n A ) )
    sing2 : (A  → (OpPointedTimesZeroMagmaTerm2 n A ) )
    0OL2 : (OpPointedTimesZeroMagmaTerm2 n A ) 
    *OL2 : ((OpPointedTimesZeroMagmaTerm2 n A )  → ((OpPointedTimesZeroMagmaTerm2 n A )  → (OpPointedTimesZeroMagmaTerm2 n A ) )) 
  
  simplifyB : (PointedTimesZeroMagmaTerm  → PointedTimesZeroMagmaTerm )
  simplifyB 0L  = 0L 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClPointedTimesZeroMagmaTerm A ) → (ClPointedTimesZeroMagmaTerm A )))
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPointedTimesZeroMagmaTerm n ) → (OpPointedTimesZeroMagmaTerm n )))
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedTimesZeroMagmaTerm2 n A ) → (OpPointedTimesZeroMagmaTerm2 n A )))
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PointedTimesZeroMagma A ) → (PointedTimesZeroMagmaTerm  → A )))
  evalB Po 0L  = (0ᵢ Po ) 
  
  evalB Po (*L x1 x2 )  = ((* Po ) (evalB Po x1 ) (evalB Po x2 ) )
  
  evalCl : ({A  : Set }  → ((PointedTimesZeroMagma A ) → ((ClPointedTimesZeroMagmaTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po 0Cl  = (0ᵢ Po ) 
  
  evalCl Po (*Cl x1 x2 )  = ((* Po ) (evalCl Po x1 ) (evalCl Po x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PointedTimesZeroMagma A ) → ((Vec A n ) → ((OpPointedTimesZeroMagmaTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars 0OL  = (0ᵢ Po ) 
  
  evalOp n Po vars (*OL x1 x2 )  = ((* Po ) (evalOp n Po vars x1 ) (evalOp n Po vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PointedTimesZeroMagma A ) → ((Vec A n ) → ((OpPointedTimesZeroMagmaTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars 0OL2  = (0ᵢ Po ) 
  
  evalOpE n Po vars (*OL2 x1 x2 )  = ((* Po ) (evalOpE n Po vars x1 ) (evalOpE n Po vars x2 ) )
  
  inductionB : ((P  : (PointedTimesZeroMagmaTerm  → Set ))  → ((P 0L ) → (((x1 x2  : PointedTimesZeroMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : PointedTimesZeroMagmaTerm )  → (P x )))))
  inductionB p p0l p*l 0L  = p0l 
  
  inductionB p p0l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p0l p*l x1 ) (inductionB p p0l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClPointedTimesZeroMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClPointedTimesZeroMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClPointedTimesZeroMagmaTerm A ))  → (P x ))))))
  inductionCl _ p psing p0cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl p*cl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p0cl p*cl x1 ) (inductionCl _ p psing p0cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpPointedTimesZeroMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpPointedTimesZeroMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpPointedTimesZeroMagmaTerm n ))  → (P x ))))))
  inductionOp _ p pv p0ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol p*ol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p0ol p*ol x1 ) (inductionOp _ p pv p0ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointedTimesZeroMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpPointedTimesZeroMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpPointedTimesZeroMagmaTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p*ol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 p*ol2 x2 ) )
  
  0L' : (  PointedTimesZeroMagmaTerm  )
  0L'  = 0L 
  
  *L' : (  (PointedTimesZeroMagmaTerm   → (PointedTimesZeroMagmaTerm   → PointedTimesZeroMagmaTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (PointedTimesZeroMagmaTerm  → (Staged PointedTimesZeroMagmaTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClPointedTimesZeroMagmaTerm A ) )
  0Cl'  = 0Cl 
  
  *Cl' : ({A  : Set }  → ((ClPointedTimesZeroMagmaTerm A )  → ((ClPointedTimesZeroMagmaTerm A )  → (ClPointedTimesZeroMagmaTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClPointedTimesZeroMagmaTerm A ) → (Staged (ClPointedTimesZeroMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpPointedTimesZeroMagmaTerm n ) )
  0OL'  = 0OL 
  
  *OL' : ({n  : Nat}  → ((OpPointedTimesZeroMagmaTerm n )  → ((OpPointedTimesZeroMagmaTerm n )  → (OpPointedTimesZeroMagmaTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpPointedTimesZeroMagmaTerm n ) → (Staged (OpPointedTimesZeroMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpPointedTimesZeroMagmaTerm2 n A ) )
  0OL2'  = 0OL2 
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpPointedTimesZeroMagmaTerm2 n A )  → ((OpPointedTimesZeroMagmaTerm2 n A )  → (OpPointedTimesZeroMagmaTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedTimesZeroMagmaTerm2 n A ) → (Staged (OpPointedTimesZeroMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
