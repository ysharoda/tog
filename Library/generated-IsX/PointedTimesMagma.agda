
 module PointedTimesMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPointedTimesMagma (A  : Set ) (*  : (A  → (A  → A ))) (e  : A )  : Set where
    constructor IsPointedTimesMagmaC
   
  
  record PointedTimesMagma (A  : Set )  : Set where
    constructor PointedTimesMagmaC
    field
      * : (A  → (A  → A ))
      e : A 
      isPointedTimesMagma : (IsPointedTimesMagma A (*) e ) 
  
  open PointedTimesMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      *S : (AS  → (AS  → AS ))
      eS : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP ) 
  
  record Hom (A1 A2  : Set ) (Po1  : (PointedTimesMagma A1 )) (Po2  : (PointedTimesMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Po1 ) x1 x2 ) ) ≡ ((* Po2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Po1 )  ) ≡ (e Po2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Po1  : (PointedTimesMagma A1 )) (Po2  : (PointedTimesMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Po1 ) x1 x2 ) ((* Po2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Po1 )  (e Po2 )  )) 
  
  data PointedTimesMagmaTerm  : Set where
    *L : (PointedTimesMagmaTerm   → (PointedTimesMagmaTerm   → PointedTimesMagmaTerm  ))
    eL : PointedTimesMagmaTerm   
  
  data ClPointedTimesMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClPointedTimesMagmaTerm A ) )
    *Cl : ((ClPointedTimesMagmaTerm A )  → ((ClPointedTimesMagmaTerm A )  → (ClPointedTimesMagmaTerm A ) ))
    eCl : (ClPointedTimesMagmaTerm A )  
  
  data OpPointedTimesMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPointedTimesMagmaTerm n ) )
    *OL : ((OpPointedTimesMagmaTerm n )  → ((OpPointedTimesMagmaTerm n )  → (OpPointedTimesMagmaTerm n ) ))
    eOL : (OpPointedTimesMagmaTerm n )  
  
  data OpPointedTimesMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPointedTimesMagmaTerm2 n A ) )
    sing2 : (A  → (OpPointedTimesMagmaTerm2 n A ) )
    *OL2 : ((OpPointedTimesMagmaTerm2 n A )  → ((OpPointedTimesMagmaTerm2 n A )  → (OpPointedTimesMagmaTerm2 n A ) ))
    eOL2 : (OpPointedTimesMagmaTerm2 n A )  
  
  simplifyB : (PointedTimesMagmaTerm  → PointedTimesMagmaTerm )
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB eL  = eL 
  
  simplifyCl : ((A  : Set )  → ((ClPointedTimesMagmaTerm A ) → (ClPointedTimesMagmaTerm A )))
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPointedTimesMagmaTerm n ) → (OpPointedTimesMagmaTerm n )))
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedTimesMagmaTerm2 n A ) → (OpPointedTimesMagmaTerm2 n A )))
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PointedTimesMagma A ) → (PointedTimesMagmaTerm  → A )))
  evalB Po (*L x1 x2 )  = ((* Po ) (evalB Po x1 ) (evalB Po x2 ) )
  
  evalB Po eL  = (e Po ) 
  
  evalCl : ({A  : Set }  → ((PointedTimesMagma A ) → ((ClPointedTimesMagmaTerm A ) → A )))
  evalCl Po (sing x1 )  = x1 
  
  evalCl Po (*Cl x1 x2 )  = ((* Po ) (evalCl Po x1 ) (evalCl Po x2 ) )
  
  evalCl Po eCl  = (e Po ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PointedTimesMagma A ) → ((Vec A n ) → ((OpPointedTimesMagmaTerm n ) → A ))))
  evalOp n Po vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Po vars (*OL x1 x2 )  = ((* Po ) (evalOp n Po vars x1 ) (evalOp n Po vars x2 ) )
  
  evalOp n Po vars eOL  = (e Po ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PointedTimesMagma A ) → ((Vec A n ) → ((OpPointedTimesMagmaTerm2 n A ) → A ))))
  evalOpE n Po vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Po vars (sing2 x1 )  = x1 
  
  evalOpE n Po vars (*OL2 x1 x2 )  = ((* Po ) (evalOpE n Po vars x1 ) (evalOpE n Po vars x2 ) )
  
  evalOpE n Po vars eOL2  = (e Po ) 
  
  inductionB : ((P  : (PointedTimesMagmaTerm  → Set ))  → (((x1 x2  : PointedTimesMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((P eL ) → ((x  : PointedTimesMagmaTerm )  → (P x )))))
  inductionB p p*l pel (*L x1 x2 )  = (p*l _ _ (inductionB p p*l pel x1 ) (inductionB p p*l pel x2 ) )
  
  inductionB p p*l pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClPointedTimesMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClPointedTimesMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClPointedTimesMagmaTerm A ))  → (P x ))))))
  inductionCl _ p psing p*cl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p*cl pecl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p*cl pecl x1 ) (inductionCl _ p psing p*cl pecl x2 ) )
  
  inductionCl _ p psing p*cl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpPointedTimesMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpPointedTimesMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpPointedTimesMagmaTerm n ))  → (P x ))))))
  inductionOp _ p pv p*ol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p*ol peol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p*ol peol x1 ) (inductionOp _ p pv p*ol peol x2 ) )
  
  inductionOp _ p pv p*ol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPointedTimesMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpPointedTimesMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpPointedTimesMagmaTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p*ol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 peol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p*ol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 p*ol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 p*ol2 peol2 eOL2  = peol2 
  
  *L' : (  (PointedTimesMagmaTerm   → (PointedTimesMagmaTerm   → PointedTimesMagmaTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  eL' : (  PointedTimesMagmaTerm  )
  eL'  = eL 
  
  stageB : (PointedTimesMagmaTerm  → (Staged PointedTimesMagmaTerm  ))
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  *Cl' : ({A  : Set }  → ((ClPointedTimesMagmaTerm A )  → ((ClPointedTimesMagmaTerm A )  → (ClPointedTimesMagmaTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClPointedTimesMagmaTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClPointedTimesMagmaTerm A ) → (Staged (ClPointedTimesMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  *OL' : ({n  : Nat}  → ((OpPointedTimesMagmaTerm n )  → ((OpPointedTimesMagmaTerm n )  → (OpPointedTimesMagmaTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpPointedTimesMagmaTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpPointedTimesMagmaTerm n ) → (Staged (OpPointedTimesMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpPointedTimesMagmaTerm2 n A )  → ((OpPointedTimesMagmaTerm2 n A )  → (OpPointedTimesMagmaTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpPointedTimesMagmaTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPointedTimesMagmaTerm2 n A ) → (Staged (OpPointedTimesMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A )  
   
