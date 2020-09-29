
 module UnaryAntiDistribution  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record UnaryAntiDistribution (A  : Set )  : Set where
    constructor UnaryAntiDistributionC
    field
      prim : (A  → A )
      op : (A  → (A  → A ))
      antidis_prim_op : ({x y  : A }  → (prim (op x y ) ) ≡ (op (prim y ) (prim x ) )) 
  
  open UnaryAntiDistribution
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      primS : (AS  → AS )
      opS : (AS  → (AS  → AS )) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      primP : ((Prod AP AP ) → (Prod AP AP ))
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      antidis_prim_opP : ({xP yP  : (Prod AP AP )}  → (primP (opP xP yP ) ) ≡ (opP (primP yP ) (primP xP ) )) 
  
  record Hom (A1 A2  : Set ) (Un1  : (UnaryAntiDistribution A1 )) (Un2  : (UnaryAntiDistribution A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Un1 ) x1 ) ) ≡ ((prim Un2 ) (hom x1 ) ))
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Un1 ) x1 x2 ) ) ≡ ((op Un2 ) (hom x1 ) (hom x2 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Un1  : (UnaryAntiDistribution A1 )) (Un2  : (UnaryAntiDistribution A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Un1 ) x1 ) ((prim Un2 ) y1 ) )))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Un1 ) x1 x2 ) ((op Un2 ) y1 y2 ) )))) 
  
  data UnaryAntiDistributionTerm  : Set where
    primL : (UnaryAntiDistributionTerm   → UnaryAntiDistributionTerm  )
    opL : (UnaryAntiDistributionTerm   → (UnaryAntiDistributionTerm   → UnaryAntiDistributionTerm  )) 
  
  data ClUnaryAntiDistributionTerm (A  : Set )  : Set where
    sing : (A  → (ClUnaryAntiDistributionTerm A ) )
    primCl : ((ClUnaryAntiDistributionTerm A )  → (ClUnaryAntiDistributionTerm A ) )
    opCl : ((ClUnaryAntiDistributionTerm A )  → ((ClUnaryAntiDistributionTerm A )  → (ClUnaryAntiDistributionTerm A ) )) 
  
  data OpUnaryAntiDistributionTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpUnaryAntiDistributionTerm n ) )
    primOL : ((OpUnaryAntiDistributionTerm n )  → (OpUnaryAntiDistributionTerm n ) )
    opOL : ((OpUnaryAntiDistributionTerm n )  → ((OpUnaryAntiDistributionTerm n )  → (OpUnaryAntiDistributionTerm n ) )) 
  
  data OpUnaryAntiDistributionTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpUnaryAntiDistributionTerm2 n A ) )
    sing2 : (A  → (OpUnaryAntiDistributionTerm2 n A ) )
    primOL2 : ((OpUnaryAntiDistributionTerm2 n A )  → (OpUnaryAntiDistributionTerm2 n A ) )
    opOL2 : ((OpUnaryAntiDistributionTerm2 n A )  → ((OpUnaryAntiDistributionTerm2 n A )  → (OpUnaryAntiDistributionTerm2 n A ) )) 
  
  simplifyB : (UnaryAntiDistributionTerm  → UnaryAntiDistributionTerm )
  simplifyB (opL (primL y ) (primL x ) )  = (primL (opL x y ) )
  
  simplifyB (primL x1 )  = (primL (simplifyB x1 ) )
  
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyCl : ((A  : Set )  → ((ClUnaryAntiDistributionTerm A ) → (ClUnaryAntiDistributionTerm A )))
  simplifyCl _ (opCl (primCl y ) (primCl x ) )  = (primCl (opCl x y ) )
  
  simplifyCl _ (primCl x1 )  = (primCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpUnaryAntiDistributionTerm n ) → (OpUnaryAntiDistributionTerm n )))
  simplifyOp _ (opOL (primOL y ) (primOL x ) )  = (primOL (opOL x y ) )
  
  simplifyOp _ (primOL x1 )  = (primOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpUnaryAntiDistributionTerm2 n A ) → (OpUnaryAntiDistributionTerm2 n A )))
  simplifyOpE _ _ (opOL2 (primOL2 y ) (primOL2 x ) )  = (primOL2 (opOL2 x y ) )
  
  simplifyOpE _ _ (primOL2 x1 )  = (primOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((UnaryAntiDistribution A ) → (UnaryAntiDistributionTerm  → A )))
  evalB Un (primL x1 )  = ((prim Un ) (evalB Un x1 ) )
  
  evalB Un (opL x1 x2 )  = ((op Un ) (evalB Un x1 ) (evalB Un x2 ) )
  
  evalCl : ({A  : Set }  → ((UnaryAntiDistribution A ) → ((ClUnaryAntiDistributionTerm A ) → A )))
  evalCl Un (sing x1 )  = x1 
  
  evalCl Un (primCl x1 )  = ((prim Un ) (evalCl Un x1 ) )
  
  evalCl Un (opCl x1 x2 )  = ((op Un ) (evalCl Un x1 ) (evalCl Un x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((UnaryAntiDistribution A ) → ((Vec A n ) → ((OpUnaryAntiDistributionTerm n ) → A ))))
  evalOp n Un vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Un vars (primOL x1 )  = ((prim Un ) (evalOp n Un vars x1 ) )
  
  evalOp n Un vars (opOL x1 x2 )  = ((op Un ) (evalOp n Un vars x1 ) (evalOp n Un vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((UnaryAntiDistribution A ) → ((Vec A n ) → ((OpUnaryAntiDistributionTerm2 n A ) → A ))))
  evalOpE n Un vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Un vars (sing2 x1 )  = x1 
  
  evalOpE n Un vars (primOL2 x1 )  = ((prim Un ) (evalOpE n Un vars x1 ) )
  
  evalOpE n Un vars (opOL2 x1 x2 )  = ((op Un ) (evalOpE n Un vars x1 ) (evalOpE n Un vars x2 ) )
  
  inductionB : ((P  : (UnaryAntiDistributionTerm  → Set ))  → (((x1  : UnaryAntiDistributionTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : UnaryAntiDistributionTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : UnaryAntiDistributionTerm )  → (P x )))))
  inductionB p ppriml popl (primL x1 )  = (ppriml _ (inductionB p ppriml popl x1 ) )
  
  inductionB p ppriml popl (opL x1 x2 )  = (popl _ _ (inductionB p ppriml popl x1 ) (inductionB p ppriml popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClUnaryAntiDistributionTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClUnaryAntiDistributionTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClUnaryAntiDistributionTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClUnaryAntiDistributionTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl popcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl popcl x1 ) )
  
  inductionCl _ p psing pprimcl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pprimcl popcl x1 ) (inductionCl _ p psing pprimcl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpUnaryAntiDistributionTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpUnaryAntiDistributionTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpUnaryAntiDistributionTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpUnaryAntiDistributionTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol popol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol popol x1 ) )
  
  inductionOp _ p pv pprimol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pprimol popol x1 ) (inductionOp _ p pv pprimol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpUnaryAntiDistributionTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpUnaryAntiDistributionTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpUnaryAntiDistributionTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpUnaryAntiDistributionTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x2 ) )
  
  primL' : (  (UnaryAntiDistributionTerm   → UnaryAntiDistributionTerm  ))
  primL' x1  = (primL x1 )
  
  opL' : (  (UnaryAntiDistributionTerm   → (UnaryAntiDistributionTerm   → UnaryAntiDistributionTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (UnaryAntiDistributionTerm  → (Staged UnaryAntiDistributionTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClUnaryAntiDistributionTerm A )  → (ClUnaryAntiDistributionTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  opCl' : ({A  : Set }  → ((ClUnaryAntiDistributionTerm A )  → ((ClUnaryAntiDistributionTerm A )  → (ClUnaryAntiDistributionTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClUnaryAntiDistributionTerm A ) → (Staged (ClUnaryAntiDistributionTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpUnaryAntiDistributionTerm n )  → (OpUnaryAntiDistributionTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  opOL' : ({n  : Nat}  → ((OpUnaryAntiDistributionTerm n )  → ((OpUnaryAntiDistributionTerm n )  → (OpUnaryAntiDistributionTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpUnaryAntiDistributionTerm n ) → (Staged (OpUnaryAntiDistributionTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpUnaryAntiDistributionTerm2 n A )  → (OpUnaryAntiDistributionTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpUnaryAntiDistributionTerm2 n A )  → ((OpUnaryAntiDistributionTerm2 n A )  → (OpUnaryAntiDistributionTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpUnaryAntiDistributionTerm2 n A ) → (Staged (OpUnaryAntiDistributionTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) )) 
   
