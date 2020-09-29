
 module CommutativeMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeMonoid (A  : Set )  : Set where
    constructor CommutativeMonoidC
    field
      op : (A  → (A  → A ))
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      e : A 
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x )) 
  
  open CommutativeMonoid
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      eS : AS  
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      eP : (Prod AP AP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP )
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP )) 
  
  record Hom (A1 A2  : Set ) (Co1  : (CommutativeMonoid A1 )) (Co2  : (CommutativeMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Co1 ) x1 x2 ) ) ≡ ((op Co2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Co1 )  ) ≡ (e Co2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Co1  : (CommutativeMonoid A1 )) (Co2  : (CommutativeMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Co1 ) x1 x2 ) ((op Co2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Co1 )  (e Co2 )  )) 
  
  data CommutativeMonoidTerm  : Set where
    opL : (CommutativeMonoidTerm   → (CommutativeMonoidTerm   → CommutativeMonoidTerm  ))
    eL : CommutativeMonoidTerm   
  
  data ClCommutativeMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClCommutativeMonoidTerm A ) )
    opCl : ((ClCommutativeMonoidTerm A )  → ((ClCommutativeMonoidTerm A )  → (ClCommutativeMonoidTerm A ) ))
    eCl : (ClCommutativeMonoidTerm A )  
  
  data OpCommutativeMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCommutativeMonoidTerm n ) )
    opOL : ((OpCommutativeMonoidTerm n )  → ((OpCommutativeMonoidTerm n )  → (OpCommutativeMonoidTerm n ) ))
    eOL : (OpCommutativeMonoidTerm n )  
  
  data OpCommutativeMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCommutativeMonoidTerm2 n A ) )
    sing2 : (A  → (OpCommutativeMonoidTerm2 n A ) )
    opOL2 : ((OpCommutativeMonoidTerm2 n A )  → ((OpCommutativeMonoidTerm2 n A )  → (OpCommutativeMonoidTerm2 n A ) ))
    eOL2 : (OpCommutativeMonoidTerm2 n A )  
  
  simplifyB : (CommutativeMonoidTerm  → CommutativeMonoidTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB (opL x eL )  = x 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB eL  = eL 
  
  simplifyCl : ((A  : Set )  → ((ClCommutativeMonoidTerm A ) → (ClCommutativeMonoidTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ (opCl x eCl )  = x 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpCommutativeMonoidTerm n ) → (OpCommutativeMonoidTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ (opOL x eOL )  = x 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeMonoidTerm2 n A ) → (OpCommutativeMonoidTerm2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x eOL2 )  = x 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((CommutativeMonoid A ) → (CommutativeMonoidTerm  → A )))
  evalB Co (opL x1 x2 )  = ((op Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalB Co eL  = (e Co ) 
  
  evalCl : ({A  : Set }  → ((CommutativeMonoid A ) → ((ClCommutativeMonoidTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co (opCl x1 x2 )  = ((op Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalCl Co eCl  = (e Co ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CommutativeMonoid A ) → ((Vec A n ) → ((OpCommutativeMonoidTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars (opOL x1 x2 )  = ((op Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOp n Co vars eOL  = (e Co ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CommutativeMonoid A ) → ((Vec A n ) → ((OpCommutativeMonoidTerm2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars (opOL2 x1 x2 )  = ((op Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  evalOpE n Co vars eOL2  = (e Co ) 
  
  inductionB : ((P  : (CommutativeMonoidTerm  → Set ))  → (((x1 x2  : CommutativeMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : CommutativeMonoidTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClCommutativeMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCommutativeMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClCommutativeMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpCommutativeMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCommutativeMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpCommutativeMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCommutativeMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCommutativeMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpCommutativeMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (CommutativeMonoidTerm   → (CommutativeMonoidTerm   → CommutativeMonoidTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  CommutativeMonoidTerm  )
  eL'  = eL 
  
  stageB : (CommutativeMonoidTerm  → (Staged CommutativeMonoidTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClCommutativeMonoidTerm A )  → ((ClCommutativeMonoidTerm A )  → (ClCommutativeMonoidTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClCommutativeMonoidTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClCommutativeMonoidTerm A ) → (Staged (ClCommutativeMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpCommutativeMonoidTerm n )  → ((OpCommutativeMonoidTerm n )  → (OpCommutativeMonoidTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpCommutativeMonoidTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpCommutativeMonoidTerm n ) → (Staged (OpCommutativeMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeMonoidTerm2 n A )  → ((OpCommutativeMonoidTerm2 n A )  → (OpCommutativeMonoidTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpCommutativeMonoidTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeMonoidTerm2 n A ) → (Staged (OpCommutativeMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A )  
   
