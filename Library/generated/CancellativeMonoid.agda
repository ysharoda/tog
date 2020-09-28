module CancellativeMonoid  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CancellativeMonoid (A  : Set )  : Set where
    constructor CancellativeMonoidC
    field
      op : (A  → (A  → A ))
      e : A 
      lunit_e : ({x  : A }  → (op e x ) ≡ x )
      runit_e : ({x  : A }  → (op x e ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      leftCancellative : ({x y z  : A }  → ((op z x ) ≡ (op z y ) → x  ≡ y ))
      rightCancellative : ({x y z  : A }  → ((op x z ) ≡ (op y z ) → x  ≡ y ))
  open CancellativeMonoid
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
  record Hom (A1 A2  : Set ) (Ca1  : (CancellativeMonoid A1 )) (Ca2  : (CancellativeMonoid A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ca1 ) x1 x2 ) ) ≡ ((op Ca2 ) (hom x1 ) (hom x2 ) ))
      pres-e : (  (hom (e Ca1 )  ) ≡ (e Ca2 ) )
  record RelInterp (A1 A2  : Set ) (Ca1  : (CancellativeMonoid A1 )) (Ca2  : (CancellativeMonoid A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ca1 ) x1 x2 ) ((op Ca2 ) y1 y2 ) ))))
      interp-e : (  (interp (e Ca1 )  (e Ca2 )  ))
  data CancellativeMonoidTerm  : Set where
    opL : (CancellativeMonoidTerm   → (CancellativeMonoidTerm   → CancellativeMonoidTerm  ))
    eL : CancellativeMonoidTerm  
  data ClCancellativeMonoidTerm (A  : Set )  : Set where
    sing : (A  → (ClCancellativeMonoidTerm A ) )
    opCl : ((ClCancellativeMonoidTerm A )  → ((ClCancellativeMonoidTerm A )  → (ClCancellativeMonoidTerm A ) ))
    eCl : (ClCancellativeMonoidTerm A ) 
  data OpCancellativeMonoidTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCancellativeMonoidTerm n ) )
    opOL : ((OpCancellativeMonoidTerm n )  → ((OpCancellativeMonoidTerm n )  → (OpCancellativeMonoidTerm n ) ))
    eOL : (OpCancellativeMonoidTerm n ) 
  data OpCancellativeMonoidTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCancellativeMonoidTerm2 n A ) )
    sing2 : (A  → (OpCancellativeMonoidTerm2 n A ) )
    opOL2 : ((OpCancellativeMonoidTerm2 n A )  → ((OpCancellativeMonoidTerm2 n A )  → (OpCancellativeMonoidTerm2 n A ) ))
    eOL2 : (OpCancellativeMonoidTerm2 n A ) 
  evalB : ({A  : Set }  → ((CancellativeMonoid A ) → (CancellativeMonoidTerm  → A )))
  evalB Ca (opL x1 x2 )  = ((op Ca ) (evalB Ca x1 ) (evalB Ca x2 ) )
  
  evalB Ca eL  = (e Ca ) 
  
  evalCl : ({A  : Set }  → ((CancellativeMonoid A ) → ((ClCancellativeMonoidTerm A ) → A )))
  evalCl Ca (sing x1 )  = x1 
  
  evalCl Ca (opCl x1 x2 )  = ((op Ca ) (evalCl Ca x1 ) (evalCl Ca x2 ) )
  
  evalCl Ca eCl  = (e Ca ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CancellativeMonoid A ) → ((Vec A n ) → ((OpCancellativeMonoidTerm n ) → A ))))
  evalOp n Ca vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ca vars (opOL x1 x2 )  = ((op Ca ) (evalOp n Ca vars x1 ) (evalOp n Ca vars x2 ) )
  
  evalOp n Ca vars eOL  = (e Ca ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CancellativeMonoid A ) → ((Vec A n ) → ((OpCancellativeMonoidTerm2 n A ) → A ))))
  evalOpE n Ca vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ca vars (sing2 x1 )  = x1 
  
  evalOpE n Ca vars (opOL2 x1 x2 )  = ((op Ca ) (evalOpE n Ca vars x1 ) (evalOpE n Ca vars x2 ) )
  
  evalOpE n Ca vars eOL2  = (e Ca ) 
  
  inductionB : ((P  : (CancellativeMonoidTerm  → Set ))  → (((x1 x2  : CancellativeMonoidTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P eL ) → ((x  : CancellativeMonoidTerm )  → (P x )))))
  inductionB p popl pel (opL x1 x2 )  = (popl _ _ (inductionB p popl pel x1 ) (inductionB p popl pel x2 ) )
  
  inductionB p popl pel eL  = pel 
  
  inductionCl : ((A  : Set ) (P  : ((ClCancellativeMonoidTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCancellativeMonoidTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P eCl ) → ((x  : (ClCancellativeMonoidTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pecl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pecl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pecl x1 ) (inductionCl _ p psing popcl pecl x2 ) )
  
  inductionCl _ p psing popcl pecl eCl  = pecl 
  
  inductionOp : ((n  : Nat) (P  : ((OpCancellativeMonoidTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCancellativeMonoidTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P eOL ) → ((x  : (OpCancellativeMonoidTerm n ))  → (P x ))))))
  inductionOp _ p pv popol peol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol peol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol peol x1 ) (inductionOp _ p pv popol peol x2 ) )
  
  inductionOp _ p pv popol peol eOL  = peol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCancellativeMonoidTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCancellativeMonoidTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P eOL2 ) → ((x  : (OpCancellativeMonoidTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 peol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 peol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 peol2 eOL2  = peol2 
  
  opL' : (  (CancellativeMonoidTerm   → (CancellativeMonoidTerm   → CancellativeMonoidTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  eL' : (  CancellativeMonoidTerm  )
  eL'  = eL 
  
  stageB : (CancellativeMonoidTerm  → (Staged CancellativeMonoidTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB eL  = (Now eL )
  
  opCl' : ({A  : Set }  → ((ClCancellativeMonoidTerm A )  → ((ClCancellativeMonoidTerm A )  → (ClCancellativeMonoidTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  eCl' : ({A  : Set }  → (ClCancellativeMonoidTerm A ) )
  eCl'  = eCl 
  
  stageCl : ((A  : Set )  → ((ClCancellativeMonoidTerm A ) → (Staged (ClCancellativeMonoidTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ eCl  = (Now eCl )
  
  opOL' : ({n  : Nat}  → ((OpCancellativeMonoidTerm n )  → ((OpCancellativeMonoidTerm n )  → (OpCancellativeMonoidTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  eOL' : ({n  : Nat}  → (OpCancellativeMonoidTerm n ) )
  eOL'  = eOL 
  
  stageOp : ((n  : Nat)  → ((OpCancellativeMonoidTerm n ) → (Staged (OpCancellativeMonoidTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ eOL  = (Now eOL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCancellativeMonoidTerm2 n A )  → ((OpCancellativeMonoidTerm2 n A )  → (OpCancellativeMonoidTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  eOL2' : ({n  : Nat } {A  : Set }  → (OpCancellativeMonoidTerm2 n A ) )
  eOL2'  = eOL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCancellativeMonoidTerm2 n A ) → (Staged (OpCancellativeMonoidTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ eOL2  = (Now eOL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      eT : (Repr A ) 