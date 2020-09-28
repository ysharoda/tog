module Left0  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Left0 (A  : Set )  : Set where
    constructor Left0C
    field
      0ᵢ : A 
      op : (A  → (A  → A ))
      leftZero_op_0ᵢ : ({x  : A }  → (op 0ᵢ x ) ≡ 0ᵢ )
  open Left0
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      0S : AS 
      opS : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      0P : (Prod AP AP )
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      leftZero_op_0P : ({xP  : (Prod AP AP )}  → (opP 0P xP ) ≡ 0P )
  record Hom (A1 A2  : Set ) (Le1  : (Left0 A1 )) (Le2  : (Left0 A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Le1 )  ) ≡ (0ᵢ Le2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Le1 ) x1 x2 ) ) ≡ ((op Le2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Le1  : (Left0 A1 )) (Le2  : (Left0 A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Le1 )  (0ᵢ Le2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Le1 ) x1 x2 ) ((op Le2 ) y1 y2 ) ))))
  data Left0LTerm  : Set where
    0L : Left0LTerm  
    opL : (Left0LTerm   → (Left0LTerm   → Left0LTerm  ))
  data ClLeft0ClTerm (A  : Set )  : Set where
    sing : (A  → (ClLeft0ClTerm A ) )
    0Cl : (ClLeft0ClTerm A ) 
    opCl : ((ClLeft0ClTerm A )  → ((ClLeft0ClTerm A )  → (ClLeft0ClTerm A ) ))
  data OpLeft0OLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpLeft0OLTerm n ) )
    0OL : (OpLeft0OLTerm n ) 
    opOL : ((OpLeft0OLTerm n )  → ((OpLeft0OLTerm n )  → (OpLeft0OLTerm n ) ))
  data OpLeft0OL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpLeft0OL2Term2 n A ) )
    sing2 : (A  → (OpLeft0OL2Term2 n A ) )
    0OL2 : (OpLeft0OL2Term2 n A ) 
    opOL2 : ((OpLeft0OL2Term2 n A )  → ((OpLeft0OL2Term2 n A )  → (OpLeft0OL2Term2 n A ) ))
  evalB : ({A  : Set }  → ((Left0 A ) → (Left0LTerm  → A )))
  evalB Le 0L  = (0ᵢ Le ) 
  
  evalB Le (opL x1 x2 )  = ((op Le ) (evalB Le x1 ) (evalB Le x2 ) )
  
  evalCl : ({A  : Set }  → ((Left0 A ) → ((ClLeft0ClTerm A ) → A )))
  evalCl Le (sing x1 )  = x1 
  
  evalCl Le 0Cl  = (0ᵢ Le ) 
  
  evalCl Le (opCl x1 x2 )  = ((op Le ) (evalCl Le x1 ) (evalCl Le x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Left0 A ) → ((Vec A n ) → ((OpLeft0OLTerm n ) → A ))))
  evalOp n Le vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Le vars 0OL  = (0ᵢ Le ) 
  
  evalOp n Le vars (opOL x1 x2 )  = ((op Le ) (evalOp n Le vars x1 ) (evalOp n Le vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Left0 A ) → ((Vec A n ) → ((OpLeft0OL2Term2 n A ) → A ))))
  evalOpE n Le vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Le vars (sing2 x1 )  = x1 
  
  evalOpE n Le vars 0OL2  = (0ᵢ Le ) 
  
  evalOpE n Le vars (opOL2 x1 x2 )  = ((op Le ) (evalOpE n Le vars x1 ) (evalOpE n Le vars x2 ) )
  
  inductionB : ((P  : (Left0LTerm  → Set ))  → ((P 0L ) → (((x1 x2  : Left0LTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : Left0LTerm )  → (P x )))))
  inductionB p p0l popl 0L  = p0l 
  
  inductionB p p0l popl (opL x1 x2 )  = (popl _ _ (inductionB p p0l popl x1 ) (inductionB p p0l popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClLeft0ClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClLeft0ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClLeft0ClTerm A ))  → (P x ))))))
  inductionCl _ p psing p0cl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl popcl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing p0cl popcl x1 ) (inductionCl _ p psing p0cl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpLeft0OLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpLeft0OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpLeft0OLTerm n ))  → (P x ))))))
  inductionOp _ p pv p0ol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol popol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv p0ol popol x1 ) (inductionOp _ p pv p0ol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpLeft0OL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpLeft0OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpLeft0OL2Term2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 popol2 x2 ) )
  
  0L' : (  Left0LTerm  )
  0L'  = 0L 
  
  opL' : (  (Left0LTerm   → (Left0LTerm   → Left0LTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (Left0LTerm  → (Staged Left0LTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClLeft0ClTerm A ) )
  0Cl'  = 0Cl 
  
  opCl' : ({A  : Set }  → ((ClLeft0ClTerm A )  → ((ClLeft0ClTerm A )  → (ClLeft0ClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClLeft0ClTerm A ) → (Staged (ClLeft0ClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpLeft0OLTerm n ) )
  0OL'  = 0OL 
  
  opOL' : ({n  : Nat}  → ((OpLeft0OLTerm n )  → ((OpLeft0OLTerm n )  → (OpLeft0OLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpLeft0OLTerm n ) → (Staged (OpLeft0OLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpLeft0OL2Term2 n A ) )
  0OL2'  = 0OL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpLeft0OL2Term2 n A )  → ((OpLeft0OL2Term2 n A )  → (OpLeft0OL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpLeft0OL2Term2 n A ) → (Staged (OpLeft0OL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))