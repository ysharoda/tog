module CommutativeMonoid1  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record CommutativeMonoid1 (A  : Set )  : Set where
    constructor CommutativeMonoid1C
    field
      op : (A  → (A  → A ))
      1ᵢ : A 
      lunit_1ᵢ : ({x  : A }  → (op 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (op x 1ᵢ ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      commutative_op : ({x y  : A }  → (op x y ) ≡ (op y x ))
  open CommutativeMonoid1
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      1S : AS 
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      lunit_1P : ({xP  : (Prod AP AP )}  → (opP 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (opP xP 1P ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      commutative_opP : ({xP yP  : (Prod AP AP )}  → (opP xP yP ) ≡ (opP yP xP ))
  record Hom (A1 A2  : Set ) (Co1  : (CommutativeMonoid1 A1 )) (Co2  : (CommutativeMonoid1 A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Co1 ) x1 x2 ) ) ≡ ((op Co2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Co1 )  ) ≡ (1ᵢ Co2 ) )
  record RelInterp (A1 A2  : Set ) (Co1  : (CommutativeMonoid1 A1 )) (Co2  : (CommutativeMonoid1 A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Co1 ) x1 x2 ) ((op Co2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Co1 )  (1ᵢ Co2 )  ))
  data CommutativeMonoid1LTerm  : Set where
    opL : (CommutativeMonoid1LTerm   → (CommutativeMonoid1LTerm   → CommutativeMonoid1LTerm  ))
    1L : CommutativeMonoid1LTerm  
  data ClCommutativeMonoid1ClTerm (A  : Set )  : Set where
    sing : (A  → (ClCommutativeMonoid1ClTerm A ) )
    opCl : ((ClCommutativeMonoid1ClTerm A )  → ((ClCommutativeMonoid1ClTerm A )  → (ClCommutativeMonoid1ClTerm A ) ))
    1Cl : (ClCommutativeMonoid1ClTerm A ) 
  data OpCommutativeMonoid1OLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpCommutativeMonoid1OLTerm n ) )
    opOL : ((OpCommutativeMonoid1OLTerm n )  → ((OpCommutativeMonoid1OLTerm n )  → (OpCommutativeMonoid1OLTerm n ) ))
    1OL : (OpCommutativeMonoid1OLTerm n ) 
  data OpCommutativeMonoid1OL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpCommutativeMonoid1OL2Term2 n A ) )
    sing2 : (A  → (OpCommutativeMonoid1OL2Term2 n A ) )
    opOL2 : ((OpCommutativeMonoid1OL2Term2 n A )  → ((OpCommutativeMonoid1OL2Term2 n A )  → (OpCommutativeMonoid1OL2Term2 n A ) ))
    1OL2 : (OpCommutativeMonoid1OL2Term2 n A ) 
  evalB : ({A  : Set }  → ((CommutativeMonoid1 A ) → (CommutativeMonoid1LTerm  → A )))
  evalB Co (opL x1 x2 )  = ((op Co ) (evalB Co x1 ) (evalB Co x2 ) )
  
  evalB Co 1L  = (1ᵢ Co ) 
  
  evalCl : ({A  : Set }  → ((CommutativeMonoid1 A ) → ((ClCommutativeMonoid1ClTerm A ) → A )))
  evalCl Co (sing x1 )  = x1 
  
  evalCl Co (opCl x1 x2 )  = ((op Co ) (evalCl Co x1 ) (evalCl Co x2 ) )
  
  evalCl Co 1Cl  = (1ᵢ Co ) 
  
  evalOp : ({A  : Set } (n  : Nat)  → ((CommutativeMonoid1 A ) → ((Vec A n ) → ((OpCommutativeMonoid1OLTerm n ) → A ))))
  evalOp n Co vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Co vars (opOL x1 x2 )  = ((op Co ) (evalOp n Co vars x1 ) (evalOp n Co vars x2 ) )
  
  evalOp n Co vars 1OL  = (1ᵢ Co ) 
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((CommutativeMonoid1 A ) → ((Vec A n ) → ((OpCommutativeMonoid1OL2Term2 n A ) → A ))))
  evalOpE n Co vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Co vars (sing2 x1 )  = x1 
  
  evalOpE n Co vars (opOL2 x1 x2 )  = ((op Co ) (evalOpE n Co vars x1 ) (evalOpE n Co vars x2 ) )
  
  evalOpE n Co vars 1OL2  = (1ᵢ Co ) 
  
  inductionB : ((P  : (CommutativeMonoid1LTerm  → Set ))  → (((x1 x2  : CommutativeMonoid1LTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P 1L ) → ((x  : CommutativeMonoid1LTerm )  → (P x )))))
  inductionB p popl p1l (opL x1 x2 )  = (popl _ _ (inductionB p popl p1l x1 ) (inductionB p popl p1l x2 ) )
  
  inductionB p popl p1l 1L  = p1l 
  
  inductionCl : ((A  : Set ) (P  : ((ClCommutativeMonoid1ClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClCommutativeMonoid1ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P 1Cl ) → ((x  : (ClCommutativeMonoid1ClTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl p1cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl p1cl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl p1cl x1 ) (inductionCl _ p psing popcl p1cl x2 ) )
  
  inductionCl _ p psing popcl p1cl 1Cl  = p1cl 
  
  inductionOp : ((n  : Nat) (P  : ((OpCommutativeMonoid1OLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpCommutativeMonoid1OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P 1OL ) → ((x  : (OpCommutativeMonoid1OLTerm n ))  → (P x ))))))
  inductionOp _ p pv popol p1ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol p1ol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol p1ol x1 ) (inductionOp _ p pv popol p1ol x2 ) )
  
  inductionOp _ p pv popol p1ol 1OL  = p1ol 
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpCommutativeMonoid1OL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpCommutativeMonoid1OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P 1OL2 ) → ((x  : (OpCommutativeMonoid1OL2Term2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 p1ol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 p1ol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 1OL2  = p1ol2 
  
  opL' : (  (CommutativeMonoid1LTerm   → (CommutativeMonoid1LTerm   → CommutativeMonoid1LTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  1L' : (  CommutativeMonoid1LTerm  )
  1L'  = 1L 
  
  stageB : (CommutativeMonoid1LTerm  → (Staged CommutativeMonoid1LTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  opCl' : ({A  : Set }  → ((ClCommutativeMonoid1ClTerm A )  → ((ClCommutativeMonoid1ClTerm A )  → (ClCommutativeMonoid1ClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClCommutativeMonoid1ClTerm A ) )
  1Cl'  = 1Cl 
  
  stageCl : ((A  : Set )  → ((ClCommutativeMonoid1ClTerm A ) → (Staged (ClCommutativeMonoid1ClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  opOL' : ({n  : Nat}  → ((OpCommutativeMonoid1OLTerm n )  → ((OpCommutativeMonoid1OLTerm n )  → (OpCommutativeMonoid1OLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpCommutativeMonoid1OLTerm n ) )
  1OL'  = 1OL 
  
  stageOp : ((n  : Nat)  → ((OpCommutativeMonoid1OLTerm n ) → (Staged (OpCommutativeMonoid1OLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpCommutativeMonoid1OL2Term2 n A )  → ((OpCommutativeMonoid1OL2Term2 n A )  → (OpCommutativeMonoid1OL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpCommutativeMonoid1OL2Term2 n A ) )
  1OL2'  = 1OL2 
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpCommutativeMonoid1OL2Term2 n A ) → (Staged (OpCommutativeMonoid1OL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 