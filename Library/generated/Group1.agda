
 module Group1  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record Group1 (A  : Set )  : Set where
    constructor Group1C
    field
      op : (A  → (A  → A ))
      1ᵢ : A 
      lunit_1ᵢ : ({x  : A }  → (op 1ᵢ x ) ≡ x )
      runit_1ᵢ : ({x  : A }  → (op x 1ᵢ ) ≡ x )
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      inv : (A  → A )
      leftInverse_inv_op_1ᵢ : ({x  : A }  → (op x (inv x ) ) ≡ 1ᵢ )
      rightInverse_inv_op_1ᵢ : ({x  : A }  → (op (inv x ) x ) ≡ 1ᵢ ) 
  
  open Group1
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      1S : AS 
      invS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      1P : (Prod AP AP )
      invP : ((Prod AP AP ) → (Prod AP AP ))
      lunit_1P : ({xP  : (Prod AP AP )}  → (opP 1P xP ) ≡ xP )
      runit_1P : ({xP  : (Prod AP AP )}  → (opP xP 1P ) ≡ xP )
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      leftInverse_inv_op_1P : ({xP  : (Prod AP AP )}  → (opP xP (invP xP ) ) ≡ 1P )
      rightInverse_inv_op_1P : ({xP  : (Prod AP AP )}  → (opP (invP xP ) xP ) ≡ 1P ) 
  
  record Hom (A1 A2  : Set ) (Gr1  : (Group1 A1 )) (Gr2  : (Group1 A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Gr1 ) x1 x2 ) ) ≡ ((op Gr2 ) (hom x1 ) (hom x2 ) ))
      pres-1 : (  (hom (1ᵢ Gr1 )  ) ≡ (1ᵢ Gr2 ) )
      pres-inv : ({x1  : A1}  → (hom ((inv Gr1 ) x1 ) ) ≡ ((inv Gr2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Gr1  : (Group1 A1 )) (Gr2  : (Group1 A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Gr1 ) x1 x2 ) ((op Gr2 ) y1 y2 ) ))))
      interp-1 : (  (interp (1ᵢ Gr1 )  (1ᵢ Gr2 )  ))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv Gr1 ) x1 ) ((inv Gr2 ) y1 ) ))) 
  
  data Group1LTerm  : Set where
    opL : (Group1LTerm   → (Group1LTerm   → Group1LTerm  ))
    1L : Group1LTerm  
    invL : (Group1LTerm   → Group1LTerm  ) 
  
  data ClGroup1ClTerm (A  : Set )  : Set where
    sing : (A  → (ClGroup1ClTerm A ) )
    opCl : ((ClGroup1ClTerm A )  → ((ClGroup1ClTerm A )  → (ClGroup1ClTerm A ) ))
    1Cl : (ClGroup1ClTerm A ) 
    invCl : ((ClGroup1ClTerm A )  → (ClGroup1ClTerm A ) ) 
  
  data OpGroup1OLTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpGroup1OLTerm n ) )
    opOL : ((OpGroup1OLTerm n )  → ((OpGroup1OLTerm n )  → (OpGroup1OLTerm n ) ))
    1OL : (OpGroup1OLTerm n ) 
    invOL : ((OpGroup1OLTerm n )  → (OpGroup1OLTerm n ) ) 
  
  data OpGroup1OL2Term2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpGroup1OL2Term2 n A ) )
    sing2 : (A  → (OpGroup1OL2Term2 n A ) )
    opOL2 : ((OpGroup1OL2Term2 n A )  → ((OpGroup1OL2Term2 n A )  → (OpGroup1OL2Term2 n A ) ))
    1OL2 : (OpGroup1OL2Term2 n A ) 
    invOL2 : ((OpGroup1OL2Term2 n A )  → (OpGroup1OL2Term2 n A ) ) 
  
  simplifyB : (Group1LTerm  → Group1LTerm )
  simplifyB (opL 1L x )  = x 
  
  simplifyB (opL x 1L )  = x 
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB 1L  = 1L 
  
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClGroup1ClTerm A ) → (ClGroup1ClTerm A )))
  simplifyCl _ (opCl 1Cl x )  = x 
  
  simplifyCl _ (opCl x 1Cl )  = x 
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ 1Cl  = 1Cl 
  
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpGroup1OLTerm n ) → (OpGroup1OLTerm n )))
  simplifyOp _ (opOL 1OL x )  = x 
  
  simplifyOp _ (opOL x 1OL )  = x 
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ 1OL  = 1OL 
  
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpGroup1OL2Term2 n A ) → (OpGroup1OL2Term2 n A )))
  simplifyOpE _ _ (opOL2 1OL2 x )  = x 
  
  simplifyOpE _ _ (opOL2 x 1OL2 )  = x 
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ 1OL2  = 1OL2 
  
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((Group1 A ) → (Group1LTerm  → A )))
  evalB Gr (opL x1 x2 )  = ((op Gr ) (evalB Gr x1 ) (evalB Gr x2 ) )
  
  evalB Gr 1L  = (1ᵢ Gr ) 
  
  evalB Gr (invL x1 )  = ((inv Gr ) (evalB Gr x1 ) )
  
  evalCl : ({A  : Set }  → ((Group1 A ) → ((ClGroup1ClTerm A ) → A )))
  evalCl Gr (sing x1 )  = x1 
  
  evalCl Gr (opCl x1 x2 )  = ((op Gr ) (evalCl Gr x1 ) (evalCl Gr x2 ) )
  
  evalCl Gr 1Cl  = (1ᵢ Gr ) 
  
  evalCl Gr (invCl x1 )  = ((inv Gr ) (evalCl Gr x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((Group1 A ) → ((Vec A n ) → ((OpGroup1OLTerm n ) → A ))))
  evalOp n Gr vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Gr vars (opOL x1 x2 )  = ((op Gr ) (evalOp n Gr vars x1 ) (evalOp n Gr vars x2 ) )
  
  evalOp n Gr vars 1OL  = (1ᵢ Gr ) 
  
  evalOp n Gr vars (invOL x1 )  = ((inv Gr ) (evalOp n Gr vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((Group1 A ) → ((Vec A n ) → ((OpGroup1OL2Term2 n A ) → A ))))
  evalOpE n Gr vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Gr vars (sing2 x1 )  = x1 
  
  evalOpE n Gr vars (opOL2 x1 x2 )  = ((op Gr ) (evalOpE n Gr vars x1 ) (evalOpE n Gr vars x2 ) )
  
  evalOpE n Gr vars 1OL2  = (1ᵢ Gr ) 
  
  evalOpE n Gr vars (invOL2 x1 )  = ((inv Gr ) (evalOpE n Gr vars x1 ) )
  
  inductionB : ((P  : (Group1LTerm  → Set ))  → (((x1 x2  : Group1LTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((P 1L ) → (((x1  : Group1LTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((x  : Group1LTerm )  → (P x ))))))
  inductionB p popl p1l pinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl p1l pinvl x1 ) (inductionB p popl p1l pinvl x2 ) )
  
  inductionB p popl p1l pinvl 1L  = p1l 
  
  inductionB p popl p1l pinvl (invL x1 )  = (pinvl _ (inductionB p popl p1l pinvl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClGroup1ClTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClGroup1ClTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((P 1Cl ) → (((x1  : (ClGroup1ClTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((x  : (ClGroup1ClTerm A ))  → (P x )))))))
  inductionCl _ p psing popcl p1cl pinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl p1cl pinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl p1cl pinvcl x1 ) (inductionCl _ p psing popcl p1cl pinvcl x2 ) )
  
  inductionCl _ p psing popcl p1cl pinvcl 1Cl  = p1cl 
  
  inductionCl _ p psing popcl p1cl pinvcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing popcl p1cl pinvcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpGroup1OLTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpGroup1OLTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((P 1OL ) → (((x1  : (OpGroup1OLTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((x  : (OpGroup1OLTerm n ))  → (P x )))))))
  inductionOp _ p pv popol p1ol pinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol p1ol pinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol p1ol pinvol x1 ) (inductionOp _ p pv popol p1ol pinvol x2 ) )
  
  inductionOp _ p pv popol p1ol pinvol 1OL  = p1ol 
  
  inductionOp _ p pv popol p1ol pinvol (invOL x1 )  = (pinvol _ (inductionOp _ p pv popol p1ol pinvol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpGroup1OL2Term2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpGroup1OL2Term2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((P 1OL2 ) → (((x1  : (OpGroup1OL2Term2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((x  : (OpGroup1OL2Term2 n A ))  → (P x ))))))))
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 1OL2  = p1ol2 
  
  inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 popol2 p1ol2 pinvol2 x1 ) )
  
  opL' : (  (Group1LTerm   → (Group1LTerm   → Group1LTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  1L' : (  Group1LTerm  )
  1L'  = 1L 
  
  invL' : (  (Group1LTerm   → Group1LTerm  ))
  invL' x1  = (invL x1 )
  
  stageB : (Group1LTerm  → (Staged Group1LTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB 1L  = (Now 1L )
  
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  opCl' : ({A  : Set }  → ((ClGroup1ClTerm A )  → ((ClGroup1ClTerm A )  → (ClGroup1ClTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  1Cl' : ({A  : Set }  → (ClGroup1ClTerm A ) )
  1Cl'  = 1Cl 
  
  invCl' : ({A  : Set }  → ((ClGroup1ClTerm A )  → (ClGroup1ClTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  stageCl : ((A  : Set )  → ((ClGroup1ClTerm A ) → (Staged (ClGroup1ClTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ 1Cl  = (Now 1Cl )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  opOL' : ({n  : Nat}  → ((OpGroup1OLTerm n )  → ((OpGroup1OLTerm n )  → (OpGroup1OLTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  1OL' : ({n  : Nat}  → (OpGroup1OLTerm n ) )
  1OL'  = 1OL 
  
  invOL' : ({n  : Nat}  → ((OpGroup1OLTerm n )  → (OpGroup1OLTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpGroup1OLTerm n ) → (Staged (OpGroup1OLTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ 1OL  = (Now 1OL )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpGroup1OL2Term2 n A )  → ((OpGroup1OL2Term2 n A )  → (OpGroup1OL2Term2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  1OL2' : ({n  : Nat } {A  : Set }  → (OpGroup1OL2Term2 n A ) )
  1OL2'  = 1OL2 
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpGroup1OL2Term2 n A )  → (OpGroup1OL2Term2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpGroup1OL2Term2 n A ) → (Staged (OpGroup1OL2Term2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ 1OL2  = (Now 1OL2 )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      1T : (Repr A ) 
      invT : ((Repr A )  → (Repr A ) ) 
   
