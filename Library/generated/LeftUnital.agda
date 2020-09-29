
 module LeftUnital  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record LeftUnital (A  : Set )  : Set where
    constructor LeftUnitalC
    field
      e : A 
      op : (A  → (A  → A ))
      lunit_e : ({x  : A }  → (op e x ) ≡ x ) 
  
  open LeftUnital
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      eS : AS 
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      eP : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Le1  : (LeftUnital A1 )) (Le2  : (LeftUnital A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-e : (  (hom (e Le1 )  ) ≡ (e Le2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Le1 ) x1 x2 ) ) ≡ ((op Le2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Le1  : (LeftUnital A1 )) (Le2  : (LeftUnital A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-e : (  (interp (e Le1 )  (e Le2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Le1 ) x1 x2 ) ((op Le2 ) y1 y2 ) )))) 
  
  data LeftUnitalTerm  : Set where
    eL : LeftUnitalTerm  
    opL : (LeftUnitalTerm   → (LeftUnitalTerm   → LeftUnitalTerm  )) 
  
  data ClLeftUnitalTerm (A  : Set )  : Set where
    sing : (A  → (ClLeftUnitalTerm A ) )
    eCl : (ClLeftUnitalTerm A ) 
    opCl : ((ClLeftUnitalTerm A )  → ((ClLeftUnitalTerm A )  → (ClLeftUnitalTerm A ) )) 
  
  data OpLeftUnitalTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeftUnitalTerm n ) )
    eOL : (OpLeftUnitalTerm n ) 
    opOL : ((OpLeftUnitalTerm n )  → ((OpLeftUnitalTerm n )  → (OpLeftUnitalTerm n ) )) 
  
  data OpLeftUnitalTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeftUnitalTerm2 n A ) )
    sing2 : (A  → (OpLeftUnitalTerm2 n A ) )
    eOL2 : (OpLeftUnitalTerm2 n A ) 
    opOL2 : ((OpLeftUnitalTerm2 n A )  → ((OpLeftUnitalTerm2 n A )  → (OpLeftUnitalTerm2 n A ) )) 
  
  simplifyB : (LeftUnitalTerm  → LeftUnitalTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB eL  = eL 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClLeftUnitalTerm A ) → (ClLeftUnitalTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpLeftUnitalTerm n ) → (OpLeftUnitalTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftUnitalTerm2 n A ) → (OpLeftUnitalTerm2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((LeftUnital A ) → (LeftUnitalTerm  → A )))
  evalB Le eL  = (e Le ) 
  
  evalB Le (opL x1 x2 )  = ((op Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((LeftUnital A ) → ((ClLeftUnitalTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le eCl  = (e Le ) 
  
  evalCl Le (opCl x1 x2 )  = ((op Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((LeftUnital A ) → ((Vec A n ) → ((OpLeftUnitalTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars eOL  = (e Le ) 
  
  evalOp n Le vars (opOL x1 x2 )  = ((op Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((LeftUnital A ) → ((Vec A n ) → ((OpLeftUnitalTerm2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars eOL2  = (e Le ) 
  
  evalOpE n Le vars (opOL2 x1 x2 )  = ((op Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (LeftUnitalTerm  → Set ))  → ((P eL ) → (((x1 x2  : LeftUnitalTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : LeftUnitalTerm )  → (P x )))))
  inductionB p pel popl eL  = pel 
  
  inductionB p pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pel popl x1 ) (inductionB p pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeftUnitalTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P eCl ) → (((x1 x2  : (ClLeftUnitalTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClLeftUnitalTerm A ))  → (P x ))))))
  inductionCl _ p psing pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pecl popcl x1 ) (inductionCl _ p psing pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeftUnitalTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P eOL ) → (((x1 x2  : (OpLeftUnitalTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpLeftUnitalTerm n ))  → (P x ))))))
  inductionOp _ p pv peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv peol popol eOL  = peol 
  
  inductionOp _ p pv peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv peol popol x1 ) (inductionOp _ p pv peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeftUnitalTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P eOL2 ) → (((x1 x2  : (OpLeftUnitalTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpLeftUnitalTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 peol2 popol2 x2 ) )
  
  eL' : (  LeftUnitalTerm  )
  eL'  = eL 
  
  opL' : (  (LeftUnitalTerm   → (LeftUnitalTerm   → LeftUnitalTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (LeftUnitalTerm  → (Staged LeftUnitalTerm  ))
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  eCl' : ({A  : Set }  → (ClLeftUnitalTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClLeftUnitalTerm A )  → ((ClLeftUnitalTerm A )  → (ClLeftUnitalTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeftUnitalTerm A ) → (Staged (ClLeftUnitalTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  eOL' : ({n  : Nat}  → (OpLeftUnitalTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpLeftUnitalTerm n )  → ((OpLeftUnitalTerm n )  → (OpLeftUnitalTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeftUnitalTerm n ) → (Staged (OpLeftUnitalTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpLeftUnitalTerm2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLeftUnitalTerm2 n A )  → ((OpLeftUnitalTerm2 n A )  → (OpLeftUnitalTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeftUnitalTerm2 n A ) → (Staged (OpLeftUnitalTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
