
 module CommutativeGroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeGroup (A  : Set )  : Set where
    constructor CommutativeGroupC
    field
      op : (A  → (A  → A ))
      e : A 
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      inv : (A  → A )
      leftInverse_inv_op_e : ({x  : A }  → (op x (inv x ) ) ≡ e )
      rightInverse_inv_op_e : ({x  : A }  → (op (inv x ) x ) ≡ e )
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x )) 
  
  open CommutativeGroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS 
      invS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      invP : ((Prod AP AP ) → (Prod AP AP ))
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP )
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      leftInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP xP (invP xP ) ) ≡ eP )
      rightInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP (invP xP ) xP ) ≡ eP )
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP )) 
  
  record Hom (A1 A2  : Set ) (Co1  : (CommutativeGroup A1 )) (Co2  : (CommutativeGroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Co1 ) x1 x2 ) ) ≡ ((op Co2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Co1 )  ) ≡ (e Co2 ) )
      pres-inv : ({x1  : A1}  → (hom ((inv Co1 ) x1 ) ) ≡ ((inv Co2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Co1  : (CommutativeGroup A1 )) (Co2  : (CommutativeGroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Co1 ) x1 x2 ) ((op Co2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Co1 )  (e Co2 )  ))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv Co1 ) x1 ) ((inv Co2 ) y1 ) ))) 
  
  data CommutativeGroupTerm  : Set where
    opL : (CommutativeGroupTerm   → (CommutativeGroupTerm   → CommutativeGroupTerm  ))
    eL : CommutativeGroupTerm  
    invL : (CommutativeGroupTerm   → CommutativeGroupTerm  ) 
  
  data ClCommutativeGroupTerm (A  : Set )  : Set where
    sing : (A  → (ClCommutativeGroupTerm A ) )
    opCl : ((ClCommutativeGroupTerm A )  → ((ClCommutativeGroupTerm A )  → (ClCommutativeGroupTerm A ) ))
    eCl : (ClCommutativeGroupTerm A ) 
    invCl : ((ClCommutativeGroupTerm A )  → (ClCommutativeGroupTerm A ) ) 
  
  data OpCommutativeGroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCommutativeGroupTerm n ) )
    opOL : ((OpCommutativeGroupTerm n )  → ((OpCommutativeGroupTerm n )  → (OpCommutativeGroupTerm n ) ))
    eOL : (OpCommutativeGroupTerm n ) 
    invOL : ((OpCommutativeGroupTerm n )  → (OpCommutativeGroupTerm n ) ) 
  
  data OpCommutativeGroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCommutativeGroupTerm2 n A ) )
    sing2 : (A  → (OpCommutativeGroupTerm2 n A ) )
    opOL2 : ((OpCommutativeGroupTerm2 n A )  → ((OpCommutativeGroupTerm2 n A )  → (OpCommutativeGroupTerm2 n A ) ))
    eOL2 : (OpCommutativeGroupTerm2 n A ) 
    invOL2 : ((OpCommutativeGroupTerm2 n A )  → (OpCommutativeGroupTerm2 n A ) ) 
  
  simplifyB : (CommutativeGroupTerm  → CommutativeGroupTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB (opL x eL )  = x 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB eL  = eL 
  
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClCommutativeGroupTerm A ) → (ClCommutativeGroupTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ (opCl x eCl )  = x 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpCommutativeGroupTerm n ) → (OpCommutativeGroupTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ (opOL x eOL )  = x 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeGroupTerm2 n A ) → (OpCommutativeGroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x eOL2 )  = x 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((CommutativeGroup A ) → (CommutativeGroupTerm  → A )))
  evalB Co (opL x1 x2 )  = ((op Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalB Co eL  = (e Co ) 
  
  evalB Co (invL x1 )  = ((inv Co ) (evalB Co x1 ) )
  
  evalCl : ({A  : Set }  → ((CommutativeGroup A ) → ((ClCommutativeGroupTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co (opCl x1 x2 )  = ((op Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalCl Co eCl  = (e Co ) 
  
  evalCl Co (invCl x1 )  = ((inv Co ) (evalCl Co x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CommutativeGroup A ) → ((Vec A n ) → ((OpCommutativeGroupTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars (opOL x1 x2 )  = ((op Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOp n Co vars eOL  = (e Co ) 
  
  evalOp n Co vars (invOL x1 )  = ((inv Co ) (evalOp n Co vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CommutativeGroup A ) → ((Vec A n ) → ((OpCommutativeGroupTerm2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars (opOL2 x1 x2 )  = ((op Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  evalOpE n Co vars eOL2  = (e Co ) 
  
  evalOpE n Co vars (invOL2 x1 )  = ((inv Co ) (evalOpE n Co vars x1 ) )
  
  inductionB : ((P  : (CommutativeGroupTerm  → Set ))  → (((x1 x2  : CommutativeGroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → (((x1  : CommutativeGroupTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((x  : CommutativeGroupTerm )  → (P x ))))))
  inductionB p popl pel pinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl pel pinvl x1 ) (inductionB p popl pel pinvl x2 ) )
  
  inductionB p popl pel pinvl eL  = pel 
  
  inductionB p popl pel pinvl (invL x1 )  = (pinvl _ (inductionB p popl pel pinvl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClCommutativeGroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCommutativeGroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → (((x1  : (ClCommutativeGroupTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((x  : (ClCommutativeGroupTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl pecl pinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl pinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl pinvcl x1 ) (inductionCl _ p psing popcl pecl pinvcl x2 ) )
  
  inductionCl _ p psing popcl pecl pinvcl eCl  = pecl 
  
  inductionCl _ p psing popcl pecl pinvcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing popcl pecl pinvcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpCommutativeGroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCommutativeGroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → (((x1  : (OpCommutativeGroupTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((x  : (OpCommutativeGroupTerm n ))  → (P x )))))))
  inductionOp _ p pv popol peol pinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol pinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol pinvol x1 ) (inductionOp _ p pv popol peol pinvol x2 ) )
  
  inductionOp _ p pv popol peol pinvol eOL  = peol 
  
  inductionOp _ p pv popol peol pinvol (invOL x1 )  = (pinvol _ (inductionOp _ p pv popol peol pinvol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCommutativeGroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCommutativeGroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → (((x1  : (OpCommutativeGroupTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((x  : (OpCommutativeGroupTerm2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 eOL2  = peol2 
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 pinvol2 x1 ) )
  
  opL' : (  (CommutativeGroupTerm   → (CommutativeGroupTerm   → CommutativeGroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  CommutativeGroupTerm  )
  eL'  = eL 
  
  invL' : (  (CommutativeGroupTerm   → CommutativeGroupTerm  ))
  invL' x1  = (invL x1 )
  
  stageB : (CommutativeGroupTerm  → (Staged CommutativeGroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  opCl' : ({A  : Set }  → ((ClCommutativeGroupTerm A )  → ((ClCommutativeGroupTerm A )  → (ClCommutativeGroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClCommutativeGroupTerm A ) )
  eCl'  = eCl 
  
  invCl' : ({A  : Set }  → ((ClCommutativeGroupTerm A )  → (ClCommutativeGroupTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  stageCl : ((A  : Set )  → ((ClCommutativeGroupTerm A ) → (Staged (ClCommutativeGroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  opOL' : ({n  : Nat}  → ((OpCommutativeGroupTerm n )  → ((OpCommutativeGroupTerm n )  → (OpCommutativeGroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpCommutativeGroupTerm n ) )
  eOL'  = eOL 
  
  invOL' : ({n  : Nat}  → ((OpCommutativeGroupTerm n )  → (OpCommutativeGroupTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpCommutativeGroupTerm n ) → (Staged (OpCommutativeGroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeGroupTerm2 n A )  → ((OpCommutativeGroupTerm2 n A )  → (OpCommutativeGroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpCommutativeGroupTerm2 n A ) )
  eOL2'  = eOL2 
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeGroupTerm2 n A )  → (OpCommutativeGroupTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeGroupTerm2 n A ) → (Staged (OpCommutativeGroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 
      invT : ((Repr A )  → (Repr A ) ) 
   
