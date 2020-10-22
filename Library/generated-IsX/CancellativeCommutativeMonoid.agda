
 module CancellativeCommutativeMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsCancellativeCommutativeMonoid (A  : Set ) (op  : (A  → (A  → A ))) (e  : A )  : Set where
    constructor IsCancellativeCommutativeMonoidC
    field
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      leftCancellative : ({x y z  : A }  → ((op z x ) ≡ (op z y ) → x  ≡ y ))
      rightCancellative : ({x y z  : A }  → ((op x z ) ≡ (op y z ) → x  ≡ y ))
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x )) 
  
  record CancellativeCommutativeMonoid (A  : Set )  : Set where
    constructor CancellativeCommutativeMonoidC
    field
      op : (A  → (A  → A ))
      e : A 
      isCancellativeCommutativeMonoid : (IsCancellativeCommutativeMonoid A op e ) 
  
  open CancellativeCommutativeMonoid
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
      lunit_eP : ({xP  : (Prod AP AP )}  → (opP eP xP ) ≡ xP )
      runit_eP : ({xP  : (Prod AP AP )}  → (opP xP eP ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      leftCancellativeP : ({xP yP zP  : (Prod AP AP )}  → ((opP zP xP ) ≡ (opP zP yP ) → xP  ≡ yP ))
      rightCancellativeP : ({xP yP zP  : (Prod AP AP )}  → ((opP xP zP ) ≡ (opP yP zP ) → xP  ≡ yP ))
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP )) 
  
  record Hom (A1 A2  : Set ) (Ca1  : (CancellativeCommutativeMonoid A1 )) (Ca2  : (CancellativeCommutativeMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ca1 ) x1 x2 ) ) ≡ ((op Ca2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Ca1 )  ) ≡ (e Ca2 ) ) 
  
  record RelInterp (A1 A2  : Set ) (Ca1  : (CancellativeCommutativeMonoid A1 )) (Ca2  : (CancellativeCommutativeMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ca1 ) x1 x2 ) ((op Ca2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Ca1 )  (e Ca2 )  )) 
  
  data CancellativeCommutativeMonoidTerm  : Set where
    opL : (CancellativeCommutativeMonoidTerm   → (CancellativeCommutativeMonoidTerm   → CancellativeCommutativeMonoidTerm  ))
    eL : CancellativeCommutativeMonoidTerm   
  
  data ClCancellativeCommutativeMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClCancellativeCommutativeMonoidTerm A ) )
    opCl : ((ClCancellativeCommutativeMonoidTerm A )  → ((ClCancellativeCommutativeMonoidTerm A )  → (ClCancellativeCommutativeMonoidTerm A ) ))
    eCl : (ClCancellativeCommutativeMonoidTerm A )  
  
  data OpCancellativeCommutativeMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCancellativeCommutativeMonoidTerm n ) )
    opOL : ((OpCancellativeCommutativeMonoidTerm n )  → ((OpCancellativeCommutativeMonoidTerm n )  → (OpCancellativeCommutativeMonoidTerm n ) ))
    eOL : (OpCancellativeCommutativeMonoidTerm n )  
  
  data OpCancellativeCommutativeMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCancellativeCommutativeMonoidTerm2 n A ) )
    sing2 : (A  → (OpCancellativeCommutativeMonoidTerm2 n A ) )
    opOL2 : ((OpCancellativeCommutativeMonoidTerm2 n A )  → ((OpCancellativeCommutativeMonoidTerm2 n A )  → (OpCancellativeCommutativeMonoidTerm2 n A ) ))
    eOL2 : (OpCancellativeCommutativeMonoidTerm2 n A )  
  
  simplifyB : (CancellativeCommutativeMonoidTerm  → CancellativeCommutativeMonoidTerm )
  simplifyB (opL eL x )  = x 
  
  simplifyB (opL x eL )  = x 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB eL  = eL 
  
  simplifyCl : ((A  : Set )  → ((ClCancellativeCommutativeMonoidTerm A ) → (ClCancellativeCommutativeMonoidTerm A )))
  simplifyCl _ (opCl eCl x )  = x 
  
  simplifyCl _ (opCl x eCl )  = x 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ eCl  = eCl 
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpCancellativeCommutativeMonoidTerm n ) → (OpCancellativeCommutativeMonoidTerm n )))
  simplifyOp _ (opOL eOL x )  = x 
  
  simplifyOp _ (opOL x eOL )  = x 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ eOL  = eOL 
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpCancellativeCommutativeMonoidTerm2 n A ) → (OpCancellativeCommutativeMonoidTerm2 n A )))
  simplifyOpE _ _ (opOL2 eOL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x eOL2 )  = x 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ eOL2  = eOL2 
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((CancellativeCommutativeMonoid A ) → (CancellativeCommutativeMonoidTerm  → A )))
  evalB Ca (opL x1 x2 )  = ((op Ca ) (evalB Ca x1 ) (evalB Ca x2 ) )
  
  evalB Ca eL  = (e Ca ) 
  
  evalCl : ({A  : Set }  → ((CancellativeCommutativeMonoid A ) → ((ClCancellativeCommutativeMonoidTerm A ) → A )))
  evalCl Ca (sing x1 )  = x1 
  
  evalCl Ca (opCl x1 x2 )  = ((op Ca ) (evalCl Ca x1 ) (evalCl Ca x2 ) )
  
  evalCl Ca eCl  = (e Ca ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CancellativeCommutativeMonoid A ) → ((Vec A n ) → ((OpCancellativeCommutativeMonoidTerm n ) → A ))))
  evalOp n Ca vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ca vars (opOL x1 x2 )  = ((op Ca ) (evalOp n Ca vars x1 ) (evalOp n Ca vars x2 ) )
  
  evalOp n Ca vars eOL  = (e Ca ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CancellativeCommutativeMonoid A ) → ((Vec A n ) → ((OpCancellativeCommutativeMonoidTerm2 n A ) → A ))))
  evalOpE n Ca vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ca vars (sing2 x1 )  = x1 
  
  evalOpE n Ca vars (opOL2 x1 x2 )  = ((op Ca ) (evalOpE n Ca vars x1 ) (evalOpE n Ca vars x2 ) )
  
  evalOpE n Ca vars eOL2  = (e Ca ) 
  
  inductionB : ((P  : (CancellativeCommutativeMonoidTerm  → Set ))  → (((x1 x2  : CancellativeCommutativeMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : CancellativeCommutativeMonoidTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClCancellativeCommutativeMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCancellativeCommutativeMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClCancellativeCommutativeMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpCancellativeCommutativeMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCancellativeCommutativeMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpCancellativeCommutativeMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCancellativeCommutativeMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCancellativeCommutativeMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpCancellativeCommutativeMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (CancellativeCommutativeMonoidTerm   → (CancellativeCommutativeMonoidTerm   → CancellativeCommutativeMonoidTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  CancellativeCommutativeMonoidTerm  )
  eL'  = eL 
  
  stageB : (CancellativeCommutativeMonoidTerm  → (Staged CancellativeCommutativeMonoidTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClCancellativeCommutativeMonoidTerm A )  → ((ClCancellativeCommutativeMonoidTerm A )  → (ClCancellativeCommutativeMonoidTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClCancellativeCommutativeMonoidTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClCancellativeCommutativeMonoidTerm A ) → (Staged (ClCancellativeCommutativeMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpCancellativeCommutativeMonoidTerm n )  → ((OpCancellativeCommutativeMonoidTerm n )  → (OpCancellativeCommutativeMonoidTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpCancellativeCommutativeMonoidTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpCancellativeCommutativeMonoidTerm n ) → (Staged (OpCancellativeCommutativeMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCancellativeCommutativeMonoidTerm2 n A )  → ((OpCancellativeCommutativeMonoidTerm2 n A )  → (OpCancellativeCommutativeMonoidTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpCancellativeCommutativeMonoidTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCancellativeCommutativeMonoidTerm2 n A ) → (Staged (OpCancellativeCommutativeMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A )  
   
