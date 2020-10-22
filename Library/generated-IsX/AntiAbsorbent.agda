
 module AntiAbsorbent  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsAntiAbsorbent (A  : Set ) (op  : (A  → (A  → A )))  : Set where
    constructor IsAntiAbsorbentC
    field
      antiAbsorbent : ({x y  : A }  → (op x (op x y ) ) ≡ y ) 
  
  record AntiAbsorbent (A  : Set )  : Set where
    constructor AntiAbsorbentC
    field
      op : (A  → (A  → A ))
      isAntiAbsorbent : (IsAntiAbsorbent A op ) 
  
  open AntiAbsorbent
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      antiAbsorbentP : ({xP yP  : (Prod AP AP )}  → (opP xP (opP xP yP ) ) ≡ yP ) 
  
  record Hom (A1 A2  : Set ) (An1  : (AntiAbsorbent A1 )) (An2  : (AntiAbsorbent A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op An1 ) x1 x2 ) ) ≡ ((op An2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (An1  : (AntiAbsorbent A1 )) (An2  : (AntiAbsorbent A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op An1 ) x1 x2 ) ((op An2 ) y1 y2 ) )))) 
  
  data AntiAbsorbentTerm  : Set where
    opL : (AntiAbsorbentTerm   → (AntiAbsorbentTerm   → AntiAbsorbentTerm  )) 
  
  data ClAntiAbsorbentTerm (A  : Set )  : Set where
    sing : (A  → (ClAntiAbsorbentTerm A ) )
    opCl : ((ClAntiAbsorbentTerm A )  → ((ClAntiAbsorbentTerm A )  → (ClAntiAbsorbentTerm A ) )) 
  
  data OpAntiAbsorbentTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpAntiAbsorbentTerm n ) )
    opOL : ((OpAntiAbsorbentTerm n )  → ((OpAntiAbsorbentTerm n )  → (OpAntiAbsorbentTerm n ) )) 
  
  data OpAntiAbsorbentTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpAntiAbsorbentTerm2 n A ) )
    sing2 : (A  → (OpAntiAbsorbentTerm2 n A ) )
    opOL2 : ((OpAntiAbsorbentTerm2 n A )  → ((OpAntiAbsorbentTerm2 n A )  → (OpAntiAbsorbentTerm2 n A ) )) 
  
  simplifyB : (AntiAbsorbentTerm  → AntiAbsorbentTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClAntiAbsorbentTerm A ) → (ClAntiAbsorbentTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpAntiAbsorbentTerm n ) → (OpAntiAbsorbentTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpAntiAbsorbentTerm2 n A ) → (OpAntiAbsorbentTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((AntiAbsorbent A ) → (AntiAbsorbentTerm  → A )))
  evalB An (opL x1 x2 )  = ((op An ) (evalB An x1 ) (evalB An x2 ) )
  
  evalCl : ({A  : Set }  → ((AntiAbsorbent A ) → ((ClAntiAbsorbentTerm A ) → A )))
  evalCl An (sing x1 )  = x1 
  
  evalCl An (opCl x1 x2 )  = ((op An ) (evalCl An x1 ) (evalCl An x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((AntiAbsorbent A ) → ((Vec A n ) → ((OpAntiAbsorbentTerm n ) → A ))))
  evalOp n An vars (v x1 )  = (lookup vars x1 )
  
  evalOp n An vars (opOL x1 x2 )  = ((op An ) (evalOp n An vars x1 ) (evalOp n An vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((AntiAbsorbent A ) → ((Vec A n ) → ((OpAntiAbsorbentTerm2 n A ) → A ))))
  evalOpE n An vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n An vars (sing2 x1 )  = x1 
  
  evalOpE n An vars (opOL2 x1 x2 )  = ((op An ) (evalOpE n An vars x1 ) (evalOpE n An vars x2 ) )
  
  inductionB : ((P  : (AntiAbsorbentTerm  → Set ))  → (((x1 x2  : AntiAbsorbentTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : AntiAbsorbentTerm )  → (P x ))))
  inductionB p popl (opL x1 x2 )  = (popl _ _ (inductionB p popl x1 ) (inductionB p popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClAntiAbsorbentTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClAntiAbsorbentTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClAntiAbsorbentTerm A ))  → (P x )))))
  inductionCl _ p psing popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl x1 ) (inductionCl _ p psing popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpAntiAbsorbentTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpAntiAbsorbentTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpAntiAbsorbentTerm n ))  → (P x )))))
  inductionOp _ p pv popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol x1 ) (inductionOp _ p pv popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpAntiAbsorbentTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpAntiAbsorbentTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpAntiAbsorbentTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 x2 ) )
  
  opL' : (  (AntiAbsorbentTerm   → (AntiAbsorbentTerm   → AntiAbsorbentTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (AntiAbsorbentTerm  → (Staged AntiAbsorbentTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  opCl' : ({A  : Set }  → ((ClAntiAbsorbentTerm A )  → ((ClAntiAbsorbentTerm A )  → (ClAntiAbsorbentTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClAntiAbsorbentTerm A ) → (Staged (ClAntiAbsorbentTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  opOL' : ({n  : Nat}  → ((OpAntiAbsorbentTerm n )  → ((OpAntiAbsorbentTerm n )  → (OpAntiAbsorbentTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpAntiAbsorbentTerm n ) → (Staged (OpAntiAbsorbentTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpAntiAbsorbentTerm2 n A )  → ((OpAntiAbsorbentTerm2 n A )  → (OpAntiAbsorbentTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpAntiAbsorbentTerm2 n A ) → (Staged (OpAntiAbsorbentTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
