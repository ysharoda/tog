
 module MoufangLaw  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record MoufangLaw (A  : Set )  : Set where
    constructor MoufangLawC
    field
      op : (A  → (A  → A ))
      moufangLaw : ({e x y z  : A }  → ((op y e )  ≡ y  → (op (op (op x y ) z ) x ) ≡ (op x (op y (op (op e z ) x ) ) ))) 
  
  open MoufangLaw
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      moufangLawP : ({eP xP yP zP  : (Prod AP AP )}  → ((opP yP eP )  ≡ yP  → (opP (opP (opP xP yP ) zP ) xP ) ≡ (opP xP (opP yP (opP (opP eP zP ) xP ) ) ))) 
  
  record Hom (A1 A2  : Set ) (Mo1  : (MoufangLaw A1 )) (Mo2  : (MoufangLaw A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Mo1 ) x1 x2 ) ) ≡ ((op Mo2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Mo1  : (MoufangLaw A1 )) (Mo2  : (MoufangLaw A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Mo1 ) x1 x2 ) ((op Mo2 ) y1 y2 ) )))) 
  
  data MoufangLawTerm  : Set where
    opL : (MoufangLawTerm   → (MoufangLawTerm   → MoufangLawTerm  )) 
  
  data ClMoufangLawTerm (A  : Set )  : Set where
    sing : (A  → (ClMoufangLawTerm A ) )
    opCl : ((ClMoufangLawTerm A )  → ((ClMoufangLawTerm A )  → (ClMoufangLawTerm A ) )) 
  
  data OpMoufangLawTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpMoufangLawTerm n ) )
    opOL : ((OpMoufangLawTerm n )  → ((OpMoufangLawTerm n )  → (OpMoufangLawTerm n ) )) 
  
  data OpMoufangLawTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpMoufangLawTerm2 n A ) )
    sing2 : (A  → (OpMoufangLawTerm2 n A ) )
    opOL2 : ((OpMoufangLawTerm2 n A )  → ((OpMoufangLawTerm2 n A )  → (OpMoufangLawTerm2 n A ) )) 
  
  simplifyB : (MoufangLawTerm  → MoufangLawTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClMoufangLawTerm A ) → (ClMoufangLawTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpMoufangLawTerm n ) → (OpMoufangLawTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpMoufangLawTerm2 n A ) → (OpMoufangLawTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((MoufangLaw A ) → (MoufangLawTerm  → A )))
  evalB Mo (opL x1 x2 )  = ((op Mo ) (evalB Mo x1 ) (evalB Mo x2 ) )
  
  evalCl : ({A  : Set }  → ((MoufangLaw A ) → ((ClMoufangLawTerm A ) → A )))
  evalCl Mo (sing x1 )  = x1 
  
  evalCl Mo (opCl x1 x2 )  = ((op Mo ) (evalCl Mo x1 ) (evalCl Mo x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((MoufangLaw A ) → ((Vec A n ) → ((OpMoufangLawTerm n ) → A ))))
  evalOp n Mo vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Mo vars (opOL x1 x2 )  = ((op Mo ) (evalOp n Mo vars x1 ) (evalOp n Mo vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((MoufangLaw A ) → ((Vec A n ) → ((OpMoufangLawTerm2 n A ) → A ))))
  evalOpE n Mo vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Mo vars (sing2 x1 )  = x1 
  
  evalOpE n Mo vars (opOL2 x1 x2 )  = ((op Mo ) (evalOpE n Mo vars x1 ) (evalOpE n Mo vars x2 ) )
  
  inductionB : ((P  : (MoufangLawTerm  → Set ))  → (((x1 x2  : MoufangLawTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : MoufangLawTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClMoufangLawTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClMoufangLawTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClMoufangLawTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpMoufangLawTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpMoufangLawTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpMoufangLawTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpMoufangLawTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpMoufangLawTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpMoufangLawTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (MoufangLawTerm   → (MoufangLawTerm   → MoufangLawTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (MoufangLawTerm  → (Staged MoufangLawTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClMoufangLawTerm A )  → ((ClMoufangLawTerm A )  → (ClMoufangLawTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClMoufangLawTerm A ) → (Staged (ClMoufangLawTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpMoufangLawTerm n )  → ((OpMoufangLawTerm n )  → (OpMoufangLawTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpMoufangLawTerm n ) → (Staged (OpMoufangLawTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpMoufangLawTerm2 n A )  → ((OpMoufangLawTerm2 n A )  → (OpMoufangLawTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpMoufangLawTerm2 n A ) → (Staged (OpMoufangLawTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
