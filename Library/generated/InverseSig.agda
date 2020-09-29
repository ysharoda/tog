
 module InverseSig  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record InverseSig (A  : Set )  : Set where
    constructor InverseSigC
    field
      inv : (A  → A )
      e : A 
      op : (A  → (A  → A )) 
  
  open InverseSig
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      invS : (AS  → AS )
      eS : AS 
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      invP : ((Prod AP AP ) → (Prod AP AP ))
      eP : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP ))) 
  
  record Hom (A1 A2  : Set ) (In1  : (InverseSig A1 )) (In2  : (InverseSig A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-inv : ({x1  : A1}  → (hom ((inv In1 ) x1 ) ) ≡ ((inv In2 ) (hom x1 ) ))
      pres-e : (  (hom (e In1 )  ) ≡ (e In2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (In1  : (InverseSig A1 )) (In2  : (InverseSig A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv In1 ) x1 ) ((inv In2 ) y1 ) )))
      interp-e : (  (interp (e In1 )  (e In2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) )))) 
  
  data InverseSigTerm  : Set where
    invL : (InverseSigTerm   → InverseSigTerm  )
    eL : InverseSigTerm  
    opL : (InverseSigTerm   → (InverseSigTerm   → InverseSigTerm  )) 
  
  data ClInverseSigTerm (A  : Set )  : Set where
    sing : (A  → (ClInverseSigTerm A ) )
    invCl : ((ClInverseSigTerm A )  → (ClInverseSigTerm A ) )
    eCl : (ClInverseSigTerm A ) 
    opCl : ((ClInverseSigTerm A )  → ((ClInverseSigTerm A )  → (ClInverseSigTerm A ) )) 
  
  data OpInverseSigTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInverseSigTerm n ) )
    invOL : ((OpInverseSigTerm n )  → (OpInverseSigTerm n ) )
    eOL : (OpInverseSigTerm n ) 
    opOL : ((OpInverseSigTerm n )  → ((OpInverseSigTerm n )  → (OpInverseSigTerm n ) )) 
  
  data OpInverseSigTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInverseSigTerm2 n A ) )
    sing2 : (A  → (OpInverseSigTerm2 n A ) )
    invOL2 : ((OpInverseSigTerm2 n A )  → (OpInverseSigTerm2 n A ) )
    eOL2 : (OpInverseSigTerm2 n A ) 
    opOL2 : ((OpInverseSigTerm2 n A )  → ((OpInverseSigTerm2 n A )  → (OpInverseSigTerm2 n A ) )) 
  
  simplifyB : (InverseSigTerm  → InverseSigTerm )
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyB eL  = eL 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClInverseSigTerm A ) → (ClInverseSigTerm A )))
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpInverseSigTerm n ) → (OpInverseSigTerm n )))
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpInverseSigTerm2 n A ) → (OpInverseSigTerm2 n A )))
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((InverseSig A ) → (InverseSigTerm  → A )))
  evalB In (invL x1 )  = ((inv In ) (evalB In x1 ) )
  
  evalB In eL  = (e In ) 
  
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalCl : ({A  : Set }  → ((InverseSig A ) → ((ClInverseSigTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (invCl x1 )  = ((inv In ) (evalCl In x1 ) )
  
  evalCl In eCl  = (e In ) 
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((InverseSig A ) → ((Vec A n ) → ((OpInverseSigTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (invOL x1 )  = ((inv In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars eOL  = (e In ) 
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((InverseSig A ) → ((Vec A n ) → ((OpInverseSigTerm2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (invOL2 x1 )  = ((inv In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars eOL2  = (e In ) 
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  inductionB : ((P  : (InverseSigTerm  → Set ))  → (((x1  : InverseSigTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((P eL ) → (((x1 x2  : InverseSigTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : InverseSigTerm )  → (P x ))))))
  inductionB p pinvl pel popl (invL x1 )  = (pinvl _ (inductionB p pinvl pel popl x1 ) )
  
  inductionB p pinvl pel popl eL  = pel 
  
  inductionB p pinvl pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pinvl pel popl x1 ) (inductionB p pinvl pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInverseSigTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInverseSigTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((P eCl ) → (((x1 x2  : (ClInverseSigTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClInverseSigTerm A ))  → (P x )))))))
  inductionCl _ p psing pinvcl pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pinvcl pecl popcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing pinvcl pecl popcl x1 ) )
  
  inductionCl _ p psing pinvcl pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pinvcl pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pinvcl pecl popcl x1 ) (inductionCl _ p psing pinvcl pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInverseSigTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInverseSigTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((P eOL ) → (((x1 x2  : (OpInverseSigTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpInverseSigTerm n ))  → (P x )))))))
  inductionOp _ p pv pinvol peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pinvol peol popol (invOL x1 )  = (pinvol _ (inductionOp _ p pv pinvol peol popol x1 ) )
  
  inductionOp _ p pv pinvol peol popol eOL  = peol 
  
  inductionOp _ p pv pinvol peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pinvol peol popol x1 ) (inductionOp _ p pv pinvol peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInverseSigTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInverseSigTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((P eOL2 ) → (((x1 x2  : (OpInverseSigTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpInverseSigTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x2 ) )
  
  invL' : (  (InverseSigTerm   → InverseSigTerm  ))
  invL' x1  = (invL x1 )
  
  eL' : (  InverseSigTerm  )
  eL'  = eL 
  
  opL' : (  (InverseSigTerm   → (InverseSigTerm   → InverseSigTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (InverseSigTerm  → (Staged InverseSigTerm  ))
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  invCl' : ({A  : Set }  → ((ClInverseSigTerm A )  → (ClInverseSigTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  eCl' : ({A  : Set }  → (ClInverseSigTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClInverseSigTerm A )  → ((ClInverseSigTerm A )  → (ClInverseSigTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClInverseSigTerm A ) → (Staged (ClInverseSigTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  invOL' : ({n  : Nat}  → ((OpInverseSigTerm n )  → (OpInverseSigTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  eOL' : ({n  : Nat}  → (OpInverseSigTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpInverseSigTerm n )  → ((OpInverseSigTerm n )  → (OpInverseSigTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpInverseSigTerm n ) → (Staged (OpInverseSigTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpInverseSigTerm2 n A )  → (OpInverseSigTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpInverseSigTerm2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInverseSigTerm2 n A )  → ((OpInverseSigTerm2 n A )  → (OpInverseSigTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInverseSigTerm2 n A ) → (Staged (OpInverseSigTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      invT : ((Repr A )  → (Repr A ) )
      eT : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
