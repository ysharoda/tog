
 module MultPointedMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsMultPointedMagma (A  : Set ) (1ᵢ  : A ) (*  : (A  → (A  → A )))  : Set where
    constructor IsMultPointedMagmaC
   
  
  record MultPointedMagma (A  : Set )  : Set where
    constructor MultPointedMagmaC
    field
      1ᵢ : A 
      * : (A  → (A  → A ))
      isMultPointedMagma : (IsMultPointedMagma A 1ᵢ (*) ) 
  
  open MultPointedMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      1S : AS 
      *S : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      1P : (Prod AP AP )
      *P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (Mu1  : (MultPointedMagma A1 )) (Mu2  : (MultPointedMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-1 : (  (hom (1ᵢ Mu1 )  ) ≡ (1ᵢ Mu2 ) )
      pres-* : ({x1  : A1} {x2  : A1}  → (hom ((* Mu1 ) x1 x2 ) ) ≡ ((* Mu2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mu1  : (MultPointedMagma A1 )) (Mu2  : (MultPointedMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-1 : (  (interp (1ᵢ Mu1 )  (1ᵢ Mu2 )  ))
      interp-* : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((* Mu1 ) x1 x2 ) ((* Mu2 ) y1 y2 ) )))) 
  
  data MultPointedMagmaTerm  : Set where
    1L : MultPointedMagmaTerm  
    *L : (MultPointedMagmaTerm   → (MultPointedMagmaTerm   → MultPointedMagmaTerm  )) 
  
  data ClMultPointedMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClMultPointedMagmaTerm A ) )
    1Cl : (ClMultPointedMagmaTerm A ) 
    *Cl : ((ClMultPointedMagmaTerm A )  → ((ClMultPointedMagmaTerm A )  → (ClMultPointedMagmaTerm A ) )) 
  
  data OpMultPointedMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMultPointedMagmaTerm n ) )
    1OL : (OpMultPointedMagmaTerm n ) 
    *OL : ((OpMultPointedMagmaTerm n )  → ((OpMultPointedMagmaTerm n )  → (OpMultPointedMagmaTerm n ) )) 
  
  data OpMultPointedMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMultPointedMagmaTerm2 n A ) )
    sing2 : (A  → (OpMultPointedMagmaTerm2 n A ) )
    1OL2 : (OpMultPointedMagmaTerm2 n A ) 
    *OL2 : ((OpMultPointedMagmaTerm2 n A )  → ((OpMultPointedMagmaTerm2 n A )  → (OpMultPointedMagmaTerm2 n A ) )) 
  
  simplifyB : (MultPointedMagmaTerm  → MultPointedMagmaTerm )
  simplifyB 1L  = 1L 
  
  simplifyB (*L x1 x2 )  = (*L (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMultPointedMagmaTerm A ) → (ClMultPointedMagmaTerm A )))
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (*Cl x1 x2 )  = (*Cl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMultPointedMagmaTerm n ) → (OpMultPointedMagmaTerm n )))
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (*OL x1 x2 )  = (*OL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMultPointedMagmaTerm2 n A ) → (OpMultPointedMagmaTerm2 n A )))
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (*OL2 x1 x2 )  = (*OL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MultPointedMagma A ) → (MultPointedMagmaTerm  → A )))
  evalB Mu 1L  = (1ᵢ Mu ) 
  
  evalB Mu (*L x1 x2 )  = ((* Mu ) (evalB Mu x1 ) (evalB Mu x2 ) )
  
  evalCl : ({A  : Set }  → ((MultPointedMagma A ) → ((ClMultPointedMagmaTerm A ) → A )))
  evalCl Mu (sing x1 )  = x1 
  
  evalCl Mu 1Cl  = (1ᵢ Mu ) 
  
  evalCl Mu (*Cl x1 x2 )  = ((* Mu ) (evalCl Mu x1 ) (evalCl Mu x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MultPointedMagma A ) → ((Vec A n ) → ((OpMultPointedMagmaTerm n ) → A ))))
  evalOp n Mu vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mu vars 1OL  = (1ᵢ Mu ) 
  
  evalOp n Mu vars (*OL x1 x2 )  = ((* Mu ) (evalOp n Mu vars x1 ) (evalOp n Mu vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MultPointedMagma A ) → ((Vec A n ) → ((OpMultPointedMagmaTerm2 n A ) → A ))))
  evalOpE n Mu vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mu vars (sing2 x1 )  = x1 
  
  evalOpE n Mu vars 1OL2  = (1ᵢ Mu ) 
  
  evalOpE n Mu vars (*OL2 x1 x2 )  = ((* Mu ) (evalOpE n Mu vars x1 ) (evalOpE n Mu vars x2 ) )
  
  inductionB : ((P  : (MultPointedMagmaTerm  → Set ))  → ((P 1L ) → (((x1 x2  : MultPointedMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (*L x1 x2 ) )))) → ((x  : MultPointedMagmaTerm )  → (P x )))))
  inductionB p p1l p*l 1L  = p1l 
  
  inductionB p p1l p*l (*L x1 x2 )  = (p*l _ _ (inductionB p p1l p*l x1 ) (inductionB p p1l p*l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMultPointedMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 1Cl ) → (((x1 x2  : (ClMultPointedMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (*Cl x1 x2 ) )))) → ((x  : (ClMultPointedMagmaTerm A ))  → (P x ))))))
  inductionCl _ p psing p1cl p*cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p1cl p*cl 1Cl  = p1cl 
  
  inductionCl _ p psing p1cl p*cl (*Cl x1 x2 )  = (p*cl _ _ (inductionCl _ p psing p1cl p*cl x1 ) (inductionCl _ p psing p1cl p*cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMultPointedMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 1OL ) → (((x1 x2  : (OpMultPointedMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (*OL x1 x2 ) )))) → ((x  : (OpMultPointedMagmaTerm n ))  → (P x ))))))
  inductionOp _ p pv p1ol p*ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p1ol p*ol 1OL  = p1ol 
  
  inductionOp _ p pv p1ol p*ol (*OL x1 x2 )  = (p*ol _ _ (inductionOp _ p pv p1ol p*ol x1 ) (inductionOp _ p pv p1ol p*ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMultPointedMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 1OL2 ) → (((x1 x2  : (OpMultPointedMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (*OL2 x1 x2 ) )))) → ((x  : (OpMultPointedMagmaTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 (*OL2 x1 x2 )  = (p*ol2 _ _ (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p1ol2 p*ol2 x2 ) )
  
  1L' : (  MultPointedMagmaTerm  )
  1L'  = 1L 
  
  *L' : (  (MultPointedMagmaTerm   → (MultPointedMagmaTerm   → MultPointedMagmaTerm  )))
  *L' x1 x2  = (*L x1 x2 )
  
  stageB : (MultPointedMagmaTerm  → (Staged MultPointedMagmaTerm  ))
  stageB 1L  = (Now 1L )
  
  stageB (*L x1 x2 )  = (stage2 *L' (codeLift2 *L' ) (stageB  x1 ) (stageB  x2 ) )
  
  1Cl' : ({A  : Set }  → (ClMultPointedMagmaTerm A ) )
  1Cl'  = 1Cl 
  
  *Cl' : ({A  : Set }  → ((ClMultPointedMagmaTerm A )  → ((ClMultPointedMagmaTerm A )  → (ClMultPointedMagmaTerm A ) )))
  *Cl' x1 x2  = (*Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMultPointedMagmaTerm A ) → (Staged (ClMultPointedMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (*Cl x1 x2 )  = (stage2 *Cl' (codeLift2 *Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  1OL' : ({n  : Nat}  → (OpMultPointedMagmaTerm n ) )
  1OL'  = 1OL 
  
  *OL' : ({n  : Nat}  → ((OpMultPointedMagmaTerm n )  → ((OpMultPointedMagmaTerm n )  → (OpMultPointedMagmaTerm n ) )))
  *OL' x1 x2  = (*OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMultPointedMagmaTerm n ) → (Staged (OpMultPointedMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (*OL x1 x2 )  = (stage2 *OL' (codeLift2 *OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpMultPointedMagmaTerm2 n A ) )
  1OL2'  = 1OL2 
  
  *OL2' : ({n  : Nat } {A  : Set }  → ((OpMultPointedMagmaTerm2 n A )  → ((OpMultPointedMagmaTerm2 n A )  → (OpMultPointedMagmaTerm2 n A ) )))
  *OL2' x1 x2  = (*OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMultPointedMagmaTerm2 n A ) → (Staged (OpMultPointedMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (*OL2 x1 x2 )  = (stage2 *OL2' (codeLift2 *OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      1T : (Repr A ) 
      *T : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
