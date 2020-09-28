module Inverse  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Inverse (A  : Set )  : Set where
    constructor InverseC
    field
      inv : (A  → A )
      e : A 
      op : (A  → (A  → A ))
      leftInverse_inv_op_e : ({x  : A }  → (op x (inv x ) ) ≡ e )
      rightInverse_inv_op_e : ({x  : A }  → (op (inv x ) x ) ≡ e )
  open Inverse
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
      leftInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP xP (invP xP ) ) ≡ eP )
      rightInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP (invP xP ) xP ) ≡ eP )
  record Hom (A1 A2  : Set ) (In1  : (Inverse A1 )) (In2  : (Inverse A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-inv : ({x1  : A1}  → (hom ((inv In1 ) x1 ) ) ≡ ((inv In2 ) (hom x1 ) ))
      pres-e : (  (hom (e In1 )  ) ≡ (e In2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op In1 ) x1 x2 ) ) ≡ ((op In2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (In1  : (Inverse A1 )) (In2  : (Inverse A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv In1 ) x1 ) ((inv In2 ) y1 ) )))
      interp-e : (  (interp (e In1 )  (e In2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op In1 ) x1 x2 ) ((op In2 ) y1 y2 ) ))))
  data InverseLTerm  : Set where
    invL : (InverseLTerm   → InverseLTerm  )
    eL : InverseLTerm  
    opL : (InverseLTerm   → (InverseLTerm   → InverseLTerm  ))
  data ClInverseClTerm (A  : Set )  : Set where
    sing : (A  → (ClInverseClTerm A ) )
    invCl : ((ClInverseClTerm A )  → (ClInverseClTerm A ) )
    eCl : (ClInverseClTerm A ) 
    opCl : ((ClInverseClTerm A )  → ((ClInverseClTerm A )  → (ClInverseClTerm A ) ))
  data OpInverseOLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpInverseOLTerm n ) )
    invOL : ((OpInverseOLTerm n )  → (OpInverseOLTerm n ) )
    eOL : (OpInverseOLTerm n ) 
    opOL : ((OpInverseOLTerm n )  → ((OpInverseOLTerm n )  → (OpInverseOLTerm n ) ))
  data OpInverseOL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpInverseOL2Term2 n A ) )
    sing2 : (A  → (OpInverseOL2Term2 n A ) )
    invOL2 : ((OpInverseOL2Term2 n A )  → (OpInverseOL2Term2 n A ) )
    eOL2 : (OpInverseOL2Term2 n A ) 
    opOL2 : ((OpInverseOL2Term2 n A )  → ((OpInverseOL2Term2 n A )  → (OpInverseOL2Term2 n A ) ))
  evalB : ({A  : Set }  → ((Inverse A ) → (InverseLTerm  → A )))
  evalB In (invL x1 )  = ((inv In ) (evalB In x1 ) )
  
  evalB In eL  = (e In ) 
  
  evalB In (opL x1 x2 )  = ((op In ) (evalB In x1 ) (evalB In x2 ) )
  
  evalCl : ({A  : Set }  → ((Inverse A ) → ((ClInverseClTerm A ) → A )))
  evalCl In (sing x1 )  = x1 
  
  evalCl In (invCl x1 )  = ((inv In ) (evalCl In x1 ) )
  
  evalCl In eCl  = (e In ) 
  
  evalCl In (opCl x1 x2 )  = ((op In ) (evalCl In x1 ) (evalCl In x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Inverse A ) → ((Vec A n ) → ((OpInverseOLTerm n ) → A ))))
  evalOp n In vars (v x1 )  = (lookup vars x1 )
  
  evalOp n In vars (invOL x1 )  = ((inv In ) (evalOp n In vars x1 ) )
  
  evalOp n In vars eOL  = (e In ) 
  
  evalOp n In vars (opOL x1 x2 )  = ((op In ) (evalOp n In vars x1 ) (evalOp n In vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Inverse A ) → ((Vec A n ) → ((OpInverseOL2Term2 n A ) → A ))))
  evalOpE n In vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n In vars (sing2 x1 )  = x1 
  
  evalOpE n In vars (invOL2 x1 )  = ((inv In ) (evalOpE n In vars x1 ) )
  
  evalOpE n In vars eOL2  = (e In ) 
  
  evalOpE n In vars (opOL2 x1 x2 )  = ((op In ) (evalOpE n In vars x1 ) (evalOpE n In vars x2 ) )
  
  inductionB : ((P  : (InverseLTerm  → Set ))  → (((x1  : InverseLTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((P eL ) → (((x1 x2  : InverseLTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : InverseLTerm )  → (P x ))))))
  inductionB p pinvl pel popl (invL x1 )  = (pinvl _ (inductionB p pinvl pel popl x1 ) )
  
  inductionB p pinvl pel popl eL  = pel 
  
  inductionB p pinvl pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pinvl pel popl x1 ) (inductionB p pinvl pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClInverseClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClInverseClTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((P eCl ) → (((x1 x2  : (ClInverseClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClInverseClTerm A ))  → (P x )))))))
  inductionCl _ p psing pinvcl pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pinvcl pecl popcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing pinvcl pecl popcl x1 ) )
  
  inductionCl _ p psing pinvcl pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pinvcl pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pinvcl pecl popcl x1 ) (inductionCl _ p psing pinvcl pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpInverseOLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpInverseOLTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((P eOL ) → (((x1 x2  : (OpInverseOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpInverseOLTerm n ))  → (P x )))))))
  inductionOp _ p pv pinvol peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pinvol peol popol (invOL x1 )  = (pinvol _ (inductionOp _ p pv pinvol peol popol x1 ) )
  
  inductionOp _ p pv pinvol peol popol eOL  = peol 
  
  inductionOp _ p pv pinvol peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pinvol peol popol x1 ) (inductionOp _ p pv pinvol peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpInverseOL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpInverseOL2Term2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((P eOL2 ) → (((x1 x2  : (OpInverseOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpInverseOL2Term2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x2 ) )
  
  invL' : (  (InverseLTerm   → InverseLTerm  ))
  invL' x1  = (invL x1 )
  
  eL' : (  InverseLTerm  )
  eL'  = eL 
  
  opL' : (  (InverseLTerm   → (InverseLTerm   → InverseLTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (InverseLTerm  → (Staged InverseLTerm  ))
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  invCl' : ({A  : Set }  → ((ClInverseClTerm A )  → (ClInverseClTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  eCl' : ({A  : Set }  → (ClInverseClTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClInverseClTerm A )  → ((ClInverseClTerm A )  → (ClInverseClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClInverseClTerm A ) → (Staged (ClInverseClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  invOL' : ({n  : Nat}  → ((OpInverseOLTerm n )  → (OpInverseOLTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  eOL' : ({n  : Nat}  → (OpInverseOLTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpInverseOLTerm n )  → ((OpInverseOLTerm n )  → (OpInverseOLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpInverseOLTerm n ) → (Staged (OpInverseOLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpInverseOL2Term2 n A )  → (OpInverseOL2Term2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpInverseOL2Term2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpInverseOL2Term2 n A )  → ((OpInverseOL2Term2 n A )  → (OpInverseOL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpInverseOL2Term2 n A ) → (Staged (OpInverseOL2Term2 n A ) )))
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