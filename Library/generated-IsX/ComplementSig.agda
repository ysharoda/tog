
 module ComplementSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsComplementSig (A  : Set ) (compl  : (A  → A ))  : Set where
    constructor IsComplementSigC
   
  
  record ComplementSig (A  : Set )  : Set where
    constructor ComplementSigC
    field
      compl : (A  → A )
      isComplementSig : (IsComplementSig A compl ) 
  
  open ComplementSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      complS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      complP : ((Prod AP AP ) → (Prod AP AP )) 
  
  record Hom (A1 A2  : Set ) (Co1  : (ComplementSig A1 )) (Co2  : (ComplementSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-compl : ({x1  : A1}  → (hom ((compl Co1 ) x1 ) ) ≡ ((compl Co2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Co1  : (ComplementSig A1 )) (Co2  : (ComplementSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-compl : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((compl Co1 ) x1 ) ((compl Co2 ) y1 ) ))) 
  
  data ComplementSigTerm  : Set where
    complL : (ComplementSigTerm   → ComplementSigTerm  ) 
  
  data ClComplementSigTerm (A  : Set )  : Set where
    sing : (A  → (ClComplementSigTerm A ) )
    complCl : ((ClComplementSigTerm A )  → (ClComplementSigTerm A ) ) 
  
  data OpComplementSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpComplementSigTerm n ) )
    complOL : ((OpComplementSigTerm n )  → (OpComplementSigTerm n ) ) 
  
  data OpComplementSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpComplementSigTerm2 n A ) )
    sing2 : (A  → (OpComplementSigTerm2 n A ) )
    complOL2 : ((OpComplementSigTerm2 n A )  → (OpComplementSigTerm2 n A ) ) 
  
  simplifyB : (ComplementSigTerm  → ComplementSigTerm )
  simplifyB (complL x1 )  = (complL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClComplementSigTerm A ) → (ClComplementSigTerm A )))
  simplifyCl _ (complCl x1 )  = (complCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpComplementSigTerm n ) → (OpComplementSigTerm n )))
  simplifyOp _ (complOL x1 )  = (complOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpComplementSigTerm2 n A ) → (OpComplementSigTerm2 n A )))
  simplifyOpE _ _ (complOL2 x1 )  = (complOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((ComplementSig A ) → (ComplementSigTerm  → A )))
  evalB Co (complL x1 )  = ((compl Co ) (evalB Co x1 ) )
  
  evalCl : ({A  : Set }  → ((ComplementSig A ) → ((ClComplementSigTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co (complCl x1 )  = ((compl Co ) (evalCl Co x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((ComplementSig A ) → ((Vec A n ) → ((OpComplementSigTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars (complOL x1 )  = ((compl Co ) (evalOp n Co vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((ComplementSig A ) → ((Vec A n ) → ((OpComplementSigTerm2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars (complOL2 x1 )  = ((compl Co ) (evalOpE n Co vars x1 ) )
  
  inductionB : ((P  : (ComplementSigTerm  → Set ))  → (((x1  : ComplementSigTerm  )  → ((P x1 ) → (P (complL x1 ) ))) → ((x  : ComplementSigTerm )  → (P x ))))
  inductionB p pcompll (complL x1 )  = (pcompll _ (inductionB p pcompll x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClComplementSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClComplementSigTerm A ) )  → ((P x1 ) → (P (complCl x1 ) ))) → ((x  : (ClComplementSigTerm A ))  → (P x )))))
  inductionCl _ p psing pcomplcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pcomplcl (complCl x1 )  = (pcomplcl _ (inductionCl _ p psing pcomplcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpComplementSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpComplementSigTerm n ) )  → ((P x1 ) → (P (complOL x1 ) ))) → ((x  : (OpComplementSigTerm n ))  → (P x )))))
  inductionOp _ p pv pcomplol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pcomplol (complOL x1 )  = (pcomplol _ (inductionOp _ p pv pcomplol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpComplementSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpComplementSigTerm2 n A ) )  → ((P x1 ) → (P (complOL2 x1 ) ))) → ((x  : (OpComplementSigTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 pcomplol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pcomplol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pcomplol2 (complOL2 x1 )  = (pcomplol2 _ (inductionOpE _ _ p pv2 psing2 pcomplol2 x1 ) )
  
  complL' : (  (ComplementSigTerm   → ComplementSigTerm  ))
  complL' x1  = (complL x1 )
  
  stageB : (ComplementSigTerm  → (Staged ComplementSigTerm  ))
  stageB (complL x1 )  = (stage1 complL' (codeLift1 complL' ) (stageB  x1 ) )
  
  complCl' : ({A  : Set }  → ((ClComplementSigTerm A )  → (ClComplementSigTerm A ) ))
  complCl' x1  = (complCl x1 )
  
  stageCl : ((A  : Set )  → ((ClComplementSigTerm A ) → (Staged (ClComplementSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (complCl x1 )  = (stage1 complCl' (codeLift1 complCl' ) ((stageCl _ ) x1 ) )
  
  complOL' : ({n  : Nat}  → ((OpComplementSigTerm n )  → (OpComplementSigTerm n ) ))
  complOL' x1  = (complOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpComplementSigTerm n ) → (Staged (OpComplementSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (complOL x1 )  = (stage1 complOL' (codeLift1 complOL' ) ((stageOp _ ) x1 ) )
  
  complOL2' : ({n  : Nat } {A  : Set }  → ((OpComplementSigTerm2 n A )  → (OpComplementSigTerm2 n A ) ))
  complOL2' x1  = (complOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpComplementSigTerm2 n A ) → (Staged (OpComplementSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (complOL2 x1 )  = (stage1 complOL2' (codeLift1 complOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      complT : ((Repr A )  → (Repr A ) ) 
   
