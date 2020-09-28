module UnaryDistributes  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record UnaryDistributes (A  : Set )  : Set where
    constructor UnaryDistributesC
    field
      prim : (A  → A )
      op : (A  → (A  → A ))
      distribute_prim_op : ({x y  : A }  → (prim (op x y ) ) ≡ (op (prim x ) (prim y ) ))
  open UnaryDistributes
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
      distribute_prim_opP : ({xP yP  : (Prod AP AP )}  → (primP (opP xP yP ) ) ≡ (opP (primP xP ) (primP yP ) ))
  record Hom (A1 A2  : Set ) (Un1  : (UnaryDistributes A1 )) (Un2  : (UnaryDistributes A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-prim : ({x1  : A1}  → (hom ((prim Un1 ) x1 ) ) ≡ ((prim Un2 ) (hom x1 ) ))
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Un1 ) x1 x2 ) ) ≡ ((op Un2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Un1  : (UnaryDistributes A1 )) (Un2  : (UnaryDistributes A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-prim : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((prim Un1 ) x1 ) ((prim Un2 ) y1 ) )))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Un1 ) x1 x2 ) ((op Un2 ) y1 y2 ) ))))
  data UnaryDistributesTerm  : Set where
    primL : (UnaryDistributesTerm   → UnaryDistributesTerm  )
    opL : (UnaryDistributesTerm   → (UnaryDistributesTerm   → UnaryDistributesTerm  ))
  data ClUnaryDistributesTerm (A  : Set )  : Set where
    sing : (A  → (ClUnaryDistributesTerm A ) )
    primCl : ((ClUnaryDistributesTerm A )  → (ClUnaryDistributesTerm A ) )
    opCl : ((ClUnaryDistributesTerm A )  → ((ClUnaryDistributesTerm A )  → (ClUnaryDistributesTerm A ) ))
  data OpUnaryDistributesTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpUnaryDistributesTerm n ) )
    primOL : ((OpUnaryDistributesTerm n )  → (OpUnaryDistributesTerm n ) )
    opOL : ((OpUnaryDistributesTerm n )  → ((OpUnaryDistributesTerm n )  → (OpUnaryDistributesTerm n ) ))
  data OpUnaryDistributesTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpUnaryDistributesTerm2 n A ) )
    sing2 : (A  → (OpUnaryDistributesTerm2 n A ) )
    primOL2 : ((OpUnaryDistributesTerm2 n A )  → (OpUnaryDistributesTerm2 n A ) )
    opOL2 : ((OpUnaryDistributesTerm2 n A )  → ((OpUnaryDistributesTerm2 n A )  → (OpUnaryDistributesTerm2 n A ) ))
  evalB : ({A  : Set }  → ((UnaryDistributes A ) → (UnaryDistributesTerm  → A )))
  evalB Un (primL x1 )  = ((prim Un ) (evalB Un x1 ) )
  
  evalB Un (opL x1 x2 )  = ((op Un ) (evalB Un x1 ) (evalB Un x2 ) )
  
  evalCl : ({A  : Set }  → ((UnaryDistributes A ) → ((ClUnaryDistributesTerm A ) → A )))
  evalCl Un (sing x1 )  = x1 
  
  evalCl Un (primCl x1 )  = ((prim Un ) (evalCl Un x1 ) )
  
  evalCl Un (opCl x1 x2 )  = ((op Un ) (evalCl Un x1 ) (evalCl Un x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((UnaryDistributes A ) → ((Vec A n ) → ((OpUnaryDistributesTerm n ) → A ))))
  evalOp n Un vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Un vars (primOL x1 )  = ((prim Un ) (evalOp n Un vars x1 ) )
  
  evalOp n Un vars (opOL x1 x2 )  = ((op Un ) (evalOp n Un vars x1 ) (evalOp n Un vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((UnaryDistributes A ) → ((Vec A n ) → ((OpUnaryDistributesTerm2 n A ) → A ))))
  evalOpE n Un vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Un vars (sing2 x1 )  = x1 
  
  evalOpE n Un vars (primOL2 x1 )  = ((prim Un ) (evalOpE n Un vars x1 ) )
  
  evalOpE n Un vars (opOL2 x1 x2 )  = ((op Un ) (evalOpE n Un vars x1 ) (evalOpE n Un vars x2 ) )
  
  inductionB : ((P  : (UnaryDistributesTerm  → Set ))  → (((x1  : UnaryDistributesTerm  )  → ((P x1 ) → (P (primL x1 ) ))) → (((x1 x2  : UnaryDistributesTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → ((x  : UnaryDistributesTerm )  → (P x )))))
  inductionB p ppriml popl (primL x1 )  = (ppriml _ (inductionB p ppriml popl x1 ) )
  
  inductionB p ppriml popl (opL x1 x2 )  = (popl _ _ (inductionB p ppriml popl x1 ) (inductionB p ppriml popl x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClUnaryDistributesTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1  : (ClUnaryDistributesTerm A ) )  → ((P x1 ) → (P (primCl x1 ) ))) → (((x1 x2  : (ClUnaryDistributesTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → ((x  : (ClUnaryDistributesTerm A ))  → (P x ))))))
  inductionCl _ p psing pprimcl popcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing pprimcl popcl (primCl x1 )  = (pprimcl _ (inductionCl _ p psing pprimcl popcl x1 ) )
  
  inductionCl _ p psing pprimcl popcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing pprimcl popcl x1 ) (inductionCl _ p psing pprimcl popcl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpUnaryDistributesTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1  : (OpUnaryDistributesTerm n ) )  → ((P x1 ) → (P (primOL x1 ) ))) → (((x1 x2  : (OpUnaryDistributesTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → ((x  : (OpUnaryDistributesTerm n ))  → (P x ))))))
  inductionOp _ p pv pprimol popol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv pprimol popol (primOL x1 )  = (pprimol _ (inductionOp _ p pv pprimol popol x1 ) )
  
  inductionOp _ p pv pprimol popol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv pprimol popol x1 ) (inductionOp _ p pv pprimol popol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpUnaryDistributesTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1  : (OpUnaryDistributesTerm2 n A ) )  → ((P x1 ) → (P (primOL2 x1 ) ))) → (((x1 x2  : (OpUnaryDistributesTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → ((x  : (OpUnaryDistributesTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (primOL2 x1 )  = (pprimol2 _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) )
  
  inductionOpE _ _ p pv2 psing2 pprimol2 popol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x1 ) (inductionOpE _ _ p pv2 psing2 pprimol2 popol2 x2 ) )
  
  primL' : (  (UnaryDistributesTerm   → UnaryDistributesTerm  ))
  primL' x1  = (primL x1 )
  
  opL' : (  (UnaryDistributesTerm   → (UnaryDistributesTerm   → UnaryDistributesTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  stageB : (UnaryDistributesTerm  → (Staged UnaryDistributesTerm  ))
  stageB (primL x1 )  = (stage1 primL' (codeLift1 primL' ) (stageB  x1 ) )
  
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  primCl' : ({A  : Set }  → ((ClUnaryDistributesTerm A )  → (ClUnaryDistributesTerm A ) ))
  primCl' x1  = (primCl x1 )
  
  opCl' : ({A  : Set }  → ((ClUnaryDistributesTerm A )  → ((ClUnaryDistributesTerm A )  → (ClUnaryDistributesTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClUnaryDistributesTerm A ) → (Staged (ClUnaryDistributesTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (primCl x1 )  = (stage1 primCl' (codeLift1 primCl' ) ((stageCl _ ) x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  primOL' : ({n  : Nat}  → ((OpUnaryDistributesTerm n )  → (OpUnaryDistributesTerm n ) ))
  primOL' x1  = (primOL x1 )
  
  opOL' : ({n  : Nat}  → ((OpUnaryDistributesTerm n )  → ((OpUnaryDistributesTerm n )  → (OpUnaryDistributesTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpUnaryDistributesTerm n ) → (Staged (OpUnaryDistributesTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (primOL x1 )  = (stage1 primOL' (codeLift1 primOL' ) ((stageOp _ ) x1 ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  primOL2' : ({n  : Nat } {A  : Set }  → ((OpUnaryDistributesTerm2 n A )  → (OpUnaryDistributesTerm2 n A ) ))
  primOL2' x1  = (primOL2 x1 )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpUnaryDistributesTerm2 n A )  → ((OpUnaryDistributesTerm2 n A )  → (OpUnaryDistributesTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpUnaryDistributesTerm2 n A ) → (Staged (OpUnaryDistributesTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (primOL2 x1 )  = (stage1 primOL2' (codeLift1 primOL2' ) ((stageOpE _ _ ) x1 ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      primT : ((Repr A )  → (Repr A ) )
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))