
 module Right0  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Right0 (A  : Set )  : Set where
    constructor Right0C
    field
      0ᵢ : A 
      op : (A  → (A  → A ))
      rightZero_op_0ᵢ : ({x  : A }  → (op x 0ᵢ ) ≡ 0ᵢ ) 
  
  open Right0
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
      rightZero_op_0P : ({xP  : (Prod AP AP )}  → (opP xP 0P ) ≡ 0P ) 
  
  record Hom (A1 A2  : Set ) (Ri1  : (Right0 A1 )) (Ri2  : (Right0 A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-0 : (  (hom (0ᵢ Ri1 )  ) ≡ (0ᵢ Ri2 ) )
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Ri1 ) x1 x2 ) ) ≡ ((op Ri2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Ri1  : (Right0 A1 )) (Ri2  : (Right0 A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-0 : (  (interp (0ᵢ Ri1 )  (0ᵢ Ri2 )  ))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Ri1 ) x1 x2 ) ((op Ri2 ) y1 y2 ) )))) 
  
  data Right0LTerm  : Set where
    0L : Right0LTerm  
    opL : (Right0LTerm   → (Right0LTerm   → Right0LTerm  )) 
  
  data ClRight0ClTerm (A  : Set )  : Set where
    sing : (A  → (ClRight0ClTerm A ) )
    0Cl : (ClRight0ClTerm A ) 
    opCl : ((ClRight0ClTerm A )  → ((ClRight0ClTerm A )  → (ClRight0ClTerm A ) )) 
  
  data OpRight0OLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRight0OLTerm n ) )
    0OL : (OpRight0OLTerm n ) 
    opOL : ((OpRight0OLTerm n )  → ((OpRight0OLTerm n )  → (OpRight0OLTerm n ) )) 
  
  data OpRight0OL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRight0OL2Term2 n A ) )
    sing2 : (A  → (OpRight0OL2Term2 n A ) )
    0OL2 : (OpRight0OL2Term2 n A ) 
    opOL2 : ((OpRight0OL2Term2 n A )  → ((OpRight0OL2Term2 n A )  → (OpRight0OL2Term2 n A ) )) 
  
  simplifyB : (Right0LTerm  → Right0LTerm )
  simplifyB 0L  = 0L 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRight0ClTerm A ) → (ClRight0ClTerm A )))
  simplifyCl _ 0Cl  = 0Cl 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRight0OLTerm n ) → (OpRight0OLTerm n )))
  simplifyOp _ 0OL  = 0OL 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRight0OL2Term2 n A ) → (OpRight0OL2Term2 n A )))
  simplifyOpE _ _ 0OL2  = 0OL2 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Right0 A ) → (Right0LTerm  → A )))
  evalB Ri 0L  = (0ᵢ Ri ) 
  
  evalB Ri (opL x1 x2 )  = ((op Ri ) (evalB Ri x1 ) (evalB Ri x2 ) )
  
  evalCl : ({A  : Set }  → ((Right0 A ) → ((ClRight0ClTerm A ) → A )))
  evalCl Ri (sing x1 )  = x1 
  
  evalCl Ri 0Cl  = (0ᵢ Ri ) 
  
  evalCl Ri (opCl x1 x2 )  = ((op Ri ) (evalCl Ri x1 ) (evalCl Ri x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Right0 A ) → ((Vec A n ) → ((OpRight0OLTerm n ) → A ))))
  evalOp n Ri vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Ri vars 0OL  = (0ᵢ Ri ) 
  
  evalOp n Ri vars (opOL x1 x2 )  = ((op Ri ) (evalOp n Ri vars x1 ) (evalOp n Ri vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Right0 A ) → ((Vec A n ) → ((OpRight0OL2Term2 n A ) → A ))))
  evalOpE n Ri vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Ri vars (sing2 x1 )  = x1 
  
  evalOpE n Ri vars 0OL2  = (0ᵢ Ri ) 
  
  evalOpE n Ri vars (opOL2 x1 x2 )  = ((op Ri ) (evalOpE n Ri vars x1 ) (evalOpE n Ri vars x2 ) )
  
  inductionB : ((P  : (Right0LTerm  → Set ))  → ((P 0L ) → (((x1 x2  : Right0LTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : Right0LTerm )  → (P x )))))
  inductionB p p0l popl 0L  = p0l 
  
  inductionB p p0l popl (opL x1 x2 )  = (popl _ _ (inductionB p p0l popl x1 ) (inductionB p p0l popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRight0ClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → ((P 0Cl ) → (((x1 x2  : (ClRight0ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClRight0ClTerm A ))  → (P x ))))))
  inductionCl _ p psing p0cl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p0cl popcl 0Cl  = p0cl 
  
  inductionCl _ p psing p0cl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing p0cl popcl x1 ) (inductionCl _ p psing p0cl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRight0OLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → ((P 0OL ) → (((x1 x2  : (OpRight0OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpRight0OLTerm n ))  → (P x ))))))
  inductionOp _ p pv p0ol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p0ol popol 0OL  = p0ol 
  
  inductionOp _ p pv p0ol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv p0ol popol x1 ) (inductionOp _ p pv p0ol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRight0OL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → ((P 0OL2 ) → (((x1 x2  : (OpRight0OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpRight0OL2Term2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 0OL2  = p0ol2 
  
  inductionOpE _ _ p pv2 psing2 p0ol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 p0ol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 p0ol2 popol2 x2 ) )
  
  0L' : (  Right0LTerm  )
  0L'  = 0L 
  
  opL' : (  (Right0LTerm   → (Right0LTerm   → Right0LTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (Right0LTerm  → (Staged Right0LTerm  ))
  stageB 0L  = (Now 0L )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  0Cl' : ({A  : Set }  → (ClRight0ClTerm A ) )
  0Cl'  = 0Cl 
  
  opCl' : ({A  : Set }  → ((ClRight0ClTerm A )  → ((ClRight0ClTerm A )  → (ClRight0ClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClRight0ClTerm A ) → (Staged (ClRight0ClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ 0Cl  = (Now 0Cl )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  0OL' : ({n  : Nat}  → (OpRight0OLTerm n ) )
  0OL'  = 0OL 
  
  opOL' : ({n  : Nat}  → ((OpRight0OLTerm n )  → ((OpRight0OLTerm n )  → (OpRight0OLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpRight0OLTerm n ) → (Staged (OpRight0OLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ 0OL  = (Now 0OL )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  0OL2' : ({n  : Nat } {A  : Set }  → (OpRight0OL2Term2 n A ) )
  0OL2'  = 0OL2 
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRight0OL2Term2 n A )  → ((OpRight0OL2Term2 n A )  → (OpRight0OL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRight0OL2Term2 n A ) → (Staged (OpRight0OL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ 0OL2  = (Now 0OL2 )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      0T : (Repr A ) 
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
