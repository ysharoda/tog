
 module PseudoInvolution  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsPseudoInvolution (A  : Set ) (inv  : (A  → A )) (op  : (A  → (A  → A )))  : Set where
    constructor IsPseudoInvolutionC
    field
      quasiRightInverse_inv_op_e : ({x  : A }  → (op (op (inv x ) x ) (inv x ) ) ≡ (inv x )) 
  
  record PseudoInvolution (A  : Set )  : Set where
    constructor PseudoInvolutionC
    field
      inv : (A  → A )
      op : (A  → (A  → A ))
      isPseudoInvolution : (IsPseudoInvolution A inv op ) 
  
  open PseudoInvolution
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      invS : (AS  → AS )
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      invP : ((Prod AP AP ) → (Prod AP AP ))
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      quasiRightInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP (opP (invP xP ) xP ) (invP xP ) ) ≡ (invP xP )) 
  
  record Hom (A1 A2  : Set ) (Ps1  : (PseudoInvolution A1 )) (Ps2  : (PseudoInvolution A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-inv : ({x1  : A1}  → (hom ((inv Ps1 ) x1 ) ) ≡ ((inv Ps2 ) (hom x1 ) ))
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ps1 ) x1 x2 ) ) ≡ ((op Ps2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ps1  : (PseudoInvolution A1 )) (Ps2  : (PseudoInvolution A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv Ps1 ) x1 ) ((inv Ps2 ) y1 ) )))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ps1 ) x1 x2 ) ((op Ps2 ) y1 y2 ) )))) 
  
  data PseudoInvolutionTerm  : Set where
    invL : (PseudoInvolutionTerm   → PseudoInvolutionTerm  )
    opL : (PseudoInvolutionTerm   → (PseudoInvolutionTerm   → PseudoInvolutionTerm  )) 
  
  data ClPseudoInvolutionTerm (A  : Set )  : Set where
    sing : (A  → (ClPseudoInvolutionTerm A ) )
    invCl : ((ClPseudoInvolutionTerm A )  → (ClPseudoInvolutionTerm A ) )
    opCl : ((ClPseudoInvolutionTerm A )  → ((ClPseudoInvolutionTerm A )  → (ClPseudoInvolutionTerm A ) )) 
  
  data OpPseudoInvolutionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpPseudoInvolutionTerm n ) )
    invOL : ((OpPseudoInvolutionTerm n )  → (OpPseudoInvolutionTerm n ) )
    opOL : ((OpPseudoInvolutionTerm n )  → ((OpPseudoInvolutionTerm n )  → (OpPseudoInvolutionTerm n ) )) 
  
  data OpPseudoInvolutionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpPseudoInvolutionTerm2 n A ) )
    sing2 : (A  → (OpPseudoInvolutionTerm2 n A ) )
    invOL2 : ((OpPseudoInvolutionTerm2 n A )  → (OpPseudoInvolutionTerm2 n A ) )
    opOL2 : ((OpPseudoInvolutionTerm2 n A )  → ((OpPseudoInvolutionTerm2 n A )  → (OpPseudoInvolutionTerm2 n A ) )) 
  
  simplifyB : (PseudoInvolutionTerm  → PseudoInvolutionTerm )
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClPseudoInvolutionTerm A ) → (ClPseudoInvolutionTerm A )))
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpPseudoInvolutionTerm n ) → (OpPseudoInvolutionTerm n )))
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpPseudoInvolutionTerm2 n A ) → (OpPseudoInvolutionTerm2 n A )))
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((PseudoInvolution A ) → (PseudoInvolutionTerm  → A )))
  evalB Ps (invL x1 )  = ((inv Ps ) (evalB Ps x1 ) )
  
  evalB Ps (opL x1 x2 )  = ((op Ps ) (evalB Ps x1 ) (evalB Ps x2 ) )
  
  evalCl : ({A  : Set }  → ((PseudoInvolution A ) → ((ClPseudoInvolutionTerm A ) → A )))
  evalCl Ps (sing x1 )  = x1 
  
  evalCl Ps (invCl x1 )  = ((inv Ps ) (evalCl Ps x1 ) )
  
  evalCl Ps (opCl x1 x2 )  = ((op Ps ) (evalCl Ps x1 ) (evalCl Ps x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((PseudoInvolution A ) → ((Vec A n ) → ((OpPseudoInvolutionTerm n ) → A ))))
  evalOp n Ps vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ps vars (invOL x1 )  = ((inv Ps ) (evalOp n Ps vars x1 ) )
  
  evalOp n Ps vars (opOL x1 x2 )  = ((op Ps ) (evalOp n Ps vars x1 ) (evalOp n Ps vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((PseudoInvolution A ) → ((Vec A n ) → ((OpPseudoInvolutionTerm2 n A ) → A ))))
  evalOpE n Ps vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ps vars (sing2 x1 )  = x1 
  
  evalOpE n Ps vars (invOL2 x1 )  = ((inv Ps ) (evalOpE n Ps vars x1 ) )
  
  evalOpE n Ps vars (opOL2 x1 x2 )  = ((op Ps ) (evalOpE n Ps vars x1 ) (evalOpE n Ps vars x2 ) )
  
  inductionB : ((P  : (PseudoInvolutionTerm  → Set ))  → (((x1  : PseudoInvolutionTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → (((x1 x2  : PseudoInvolutionTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : PseudoInvolutionTerm )  → (P x )))))
  inductionB p pinvl popl (invL x1 )  = (pinvl _ (inductionB p pinvl popl x1 ) )
  
  inductionB p pinvl popl (opL x1 x2 )  = (popl _ _ (inductionB p pinvl popl x1 ) (inductionB p pinvl popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClPseudoInvolutionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClPseudoInvolutionTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → (((x1 x2  : (ClPseudoInvolutionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClPseudoInvolutionTerm A ))  → (P x ))))))
  inductionCl _ p psing pinvcl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pinvcl popcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing pinvcl popcl x1 ) )
  
  inductionCl _ p psing pinvcl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pinvcl popcl x1 ) (inductionCl _ p psing pinvcl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpPseudoInvolutionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpPseudoInvolutionTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → (((x1 x2  : (OpPseudoInvolutionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpPseudoInvolutionTerm n ))  → (P x ))))))
  inductionOp _ p pv pinvol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pinvol popol (invOL x1 )  = (pinvol _ (inductionOp _ p pv pinvol popol x1 ) )
  
  inductionOp _ p pv pinvol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pinvol popol x1 ) (inductionOp _ p pv pinvol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpPseudoInvolutionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpPseudoInvolutionTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → (((x1 x2  : (OpPseudoInvolutionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpPseudoInvolutionTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pinvol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 popol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 pinvol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pinvol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pinvol2 popol2 x2 ) )
  
  invL' : (  (PseudoInvolutionTerm   → PseudoInvolutionTerm  ))
  invL' x1  = (invL x1 )
  
  opL' : (  (PseudoInvolutionTerm   → (PseudoInvolutionTerm   → PseudoInvolutionTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (PseudoInvolutionTerm  → (Staged PseudoInvolutionTerm  ))
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  invCl' : ({A  : Set }  → ((ClPseudoInvolutionTerm A )  → (ClPseudoInvolutionTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  opCl' : ({A  : Set }  → ((ClPseudoInvolutionTerm A )  → ((ClPseudoInvolutionTerm A )  → (ClPseudoInvolutionTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClPseudoInvolutionTerm A ) → (Staged (ClPseudoInvolutionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  invOL' : ({n  : Nat}  → ((OpPseudoInvolutionTerm n )  → (OpPseudoInvolutionTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  opOL' : ({n  : Nat}  → ((OpPseudoInvolutionTerm n )  → ((OpPseudoInvolutionTerm n )  → (OpPseudoInvolutionTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpPseudoInvolutionTerm n ) → (Staged (OpPseudoInvolutionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpPseudoInvolutionTerm2 n A )  → (OpPseudoInvolutionTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpPseudoInvolutionTerm2 n A )  → ((OpPseudoInvolutionTerm2 n A )  → (OpPseudoInvolutionTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpPseudoInvolutionTerm2 n A ) → (Staged (OpPseudoInvolutionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      invT : ((Repr A )  → (Repr A ) )
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
