module RightInverse  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record RightInverse (A  : Set )  : Set where
    constructor RightInverseC
    field
      inv : (A  → A )
      e : A 
      op : (A  → (A  → A ))
      rightInverse_inv_op_e : ({x  : A }  → (op (inv x ) x ) ≡ e )
  open RightInverse
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
      rightInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP (invP xP ) xP ) ≡ eP )
  record Hom (A1 A2  : Set ) (Ri1  : (RightInverse A1 )) (Ri2  : (RightInverse A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-inv : ({x1  : A1}  → (hom ((inv Ri1 ) x1 ) ) ≡ ((inv Ri2 ) (hom x1 ) ))
      pres-e : (  (hom (e Ri1 )  ) ≡ (e Ri2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Ri1  : (RightInverse A1 )) (Ri2  : (RightInverse A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv Ri1 ) x1 ) ((inv Ri2 ) y1 ) )))
      interp-e : (  (interp (e Ri1 )  (e Ri2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) ))))
  data RightInverseLTerm  : Set where
    invL : (RightInverseLTerm   → RightInverseLTerm  )
    eL : RightInverseLTerm  
    opL : (RightInverseLTerm   → (RightInverseLTerm   → RightInverseLTerm  ))
  data ClRightInverseClTerm (A  : Set )  : Set where
    sing : (A  → (ClRightInverseClTerm A ) )
    invCl : ((ClRightInverseClTerm A )  → (ClRightInverseClTerm A ) )
    eCl : (ClRightInverseClTerm A ) 
    opCl : ((ClRightInverseClTerm A )  → ((ClRightInverseClTerm A )  → (ClRightInverseClTerm A ) ))
  data OpRightInverseOLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRightInverseOLTerm n ) )
    invOL : ((OpRightInverseOLTerm n )  → (OpRightInverseOLTerm n ) )
    eOL : (OpRightInverseOLTerm n ) 
    opOL : ((OpRightInverseOLTerm n )  → ((OpRightInverseOLTerm n )  → (OpRightInverseOLTerm n ) ))
  data OpRightInverseOL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRightInverseOL2Term2 n A ) )
    sing2 : (A  → (OpRightInverseOL2Term2 n A ) )
    invOL2 : ((OpRightInverseOL2Term2 n A )  → (OpRightInverseOL2Term2 n A ) )
    eOL2 : (OpRightInverseOL2Term2 n A ) 
    opOL2 : ((OpRightInverseOL2Term2 n A )  → ((OpRightInverseOL2Term2 n A )  → (OpRightInverseOL2Term2 n A ) ))
  evalB : ({A  : Set }  → ((RightInverse A ) → (RightInverseLTerm  → A )))
  evalB Ri (invL x1 )  = ((inv Ri ) (evalB Ri x1 ) )
  
  evalB Ri eL  = (e Ri ) 
  
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((RightInverse A ) → ((ClRightInverseClTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri (invCl x1 )  = ((inv Ri ) (evalCl Ri x1 ) )
  
  evalCl Ri eCl  = (e Ri ) 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RightInverse A ) → ((Vec A n ) → ((OpRightInverseOLTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars (invOL x1 )  = ((inv Ri ) (evalOp n Ri vars x1 ) )
  
  evalOp n Ri vars eOL  = (e Ri ) 
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RightInverse A ) → ((Vec A n ) → ((OpRightInverseOL2Term2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars (invOL2 x1 )  = ((inv Ri ) (evalOpE n Ri vars x1 ) )
  
  evalOpE n Ri vars eOL2  = (e Ri ) 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (RightInverseLTerm  → Set ))  → (((x1  : RightInverseLTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((P eL ) → (((x1 x2  : RightInverseLTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : RightInverseLTerm )  → (P x ))))))
  inductionB p pinvl pel popl (invL x1 )  = (pinvl _ (inductionB p pinvl pel popl x1 ) )
  
  inductionB p pinvl pel popl eL  = pel 
  
  inductionB p pinvl pel popl (opL x1 x2 )  = (popl _ _ (inductionB p pinvl pel popl x1 ) (inductionB p pinvl pel popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRightInverseClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClRightInverseClTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((P eCl ) → (((x1 x2  : (ClRightInverseClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClRightInverseClTerm A ))  → (P x )))))))
  inductionCl _ p psing pinvcl pecl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pinvcl pecl popcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing pinvcl pecl popcl x1 ) )
  
  inductionCl _ p psing pinvcl pecl popcl eCl  = pecl 
  
  inductionCl _ p psing pinvcl pecl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pinvcl pecl popcl x1 ) (inductionCl _ p psing pinvcl pecl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRightInverseOLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpRightInverseOLTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((P eOL ) → (((x1 x2  : (OpRightInverseOLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpRightInverseOLTerm n ))  → (P x )))))))
  inductionOp _ p pv pinvol peol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pinvol peol popol (invOL x1 )  = (pinvol _ (inductionOp _ p pv pinvol peol popol x1 ) )
  
  inductionOp _ p pv pinvol peol popol eOL  = peol 
  
  inductionOp _ p pv pinvol peol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pinvol peol popol x1 ) (inductionOp _ p pv pinvol peol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRightInverseOL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpRightInverseOL2Term2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((P eOL2 ) → (((x1 x2  : (OpRightInverseOL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpRightInverseOL2Term2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pinvol2 peol2 popol2 x2 ) )
  
  invL' : (  (RightInverseLTerm   → RightInverseLTerm  ))
  invL' x1  = (invL x1 )
  
  eL' : (  RightInverseLTerm  )
  eL'  = eL 
  
  opL' : (  (RightInverseLTerm   → (RightInverseLTerm   → RightInverseLTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (RightInverseLTerm  → (Staged RightInverseLTerm  ))
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  stageB eL  = (Now eL )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  invCl' : ({A  : Set }  → ((ClRightInverseClTerm A )  → (ClRightInverseClTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  eCl' : ({A  : Set }  → (ClRightInverseClTerm A ) )
  eCl'  = eCl 
  
  opCl' : ({A  : Set }  → ((ClRightInverseClTerm A )  → ((ClRightInverseClTerm A )  → (ClRightInverseClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRightInverseClTerm A ) → (Staged (ClRightInverseClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  invOL' : ({n  : Nat}  → ((OpRightInverseOLTerm n )  → (OpRightInverseOLTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  eOL' : ({n  : Nat}  → (OpRightInverseOLTerm n ) )
  eOL'  = eOL 
  
  opOL' : ({n  : Nat}  → ((OpRightInverseOLTerm n )  → ((OpRightInverseOLTerm n )  → (OpRightInverseOLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRightInverseOLTerm n ) → (Staged (OpRightInverseOLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpRightInverseOL2Term2 n A )  → (OpRightInverseOL2Term2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpRightInverseOL2Term2 n A ) )
  eOL2'  = eOL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRightInverseOL2Term2 n A )  → ((OpRightInverseOL2Term2 n A )  → (OpRightInverseOL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRightInverseOL2Term2 n A ) → (Staged (OpRightInverseOL2Term2 n A ) )))
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