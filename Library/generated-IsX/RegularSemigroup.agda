
 module RegularSemigroup  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IsRegularSemigroup (A  : Set ) (op  : (A  → (A  → A ))) (inv  : (A  → A ))  : Set where
    constructor IsRegularSemigroupC
    field
      associative_op : ({x y z  : A }  → (op (op x y ) z ) ≡ (op x (op y z ) ))
      quasiInverse_inv_op_e : ({x  : A }  → (op (op x (inv x ) ) x ) ≡ x ) 
  
  record RegularSemigroup (A  : Set )  : Set where
    constructor RegularSemigroupC
    field
      op : (A  → (A  → A ))
      inv : (A  → A )
      isRegularSemigroup : (IsRegularSemigroup A op inv ) 
  
  open RegularSemigroup
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      opS : (AS  → (AS  → AS ))
      invS : (AS  → AS ) 
  
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      opP : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      invP : ((Prod AP AP ) → (Prod AP AP ))
      associative_opP : ({xP yP zP  : (Prod AP AP )}  → (opP (opP xP yP ) zP ) ≡ (opP xP (opP yP zP ) ))
      quasiInverse_inv_op_eP : ({xP  : (Prod AP AP )}  → (opP (opP xP (invP xP ) ) xP ) ≡ xP ) 
  
  record Hom (A1 A2  : Set ) (Re1  : (RegularSemigroup A1 )) (Re2  : (RegularSemigroup A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-op : ({x1  : A1} {x2  : A1}  → (hom ((op Re1 ) x1 x2 ) ) ≡ ((op Re2 ) (hom x1 ) (hom x2 ) ))
      pres-inv : ({x1  : A1}  → (hom ((inv Re1 ) x1 ) ) ≡ ((inv Re2 ) (hom x1 ) )) 
  
  record RelInterp (A1 A2  : Set ) (Re1  : (RegularSemigroup A1 )) (Re2  : (RegularSemigroup A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-op : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((op Re1 ) x1 x2 ) ((op Re2 ) y1 y2 ) ))))
      interp-inv : ({x1  : A1} {y1  : A2}  → ((interp x1 y1 ) → (interp ((inv Re1 ) x1 ) ((inv Re2 ) y1 ) ))) 
  
  data RegularSemigroupTerm  : Set where
    opL : (RegularSemigroupTerm   → (RegularSemigroupTerm   → RegularSemigroupTerm  ))
    invL : (RegularSemigroupTerm   → RegularSemigroupTerm  ) 
  
  data ClRegularSemigroupTerm (A  : Set )  : Set where
    sing : (A  → (ClRegularSemigroupTerm A ) )
    opCl : ((ClRegularSemigroupTerm A )  → ((ClRegularSemigroupTerm A )  → (ClRegularSemigroupTerm A ) ))
    invCl : ((ClRegularSemigroupTerm A )  → (ClRegularSemigroupTerm A ) ) 
  
  data OpRegularSemigroupTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpRegularSemigroupTerm n ) )
    opOL : ((OpRegularSemigroupTerm n )  → ((OpRegularSemigroupTerm n )  → (OpRegularSemigroupTerm n ) ))
    invOL : ((OpRegularSemigroupTerm n )  → (OpRegularSemigroupTerm n ) ) 
  
  data OpRegularSemigroupTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpRegularSemigroupTerm2 n A ) )
    sing2 : (A  → (OpRegularSemigroupTerm2 n A ) )
    opOL2 : ((OpRegularSemigroupTerm2 n A )  → ((OpRegularSemigroupTerm2 n A )  → (OpRegularSemigroupTerm2 n A ) ))
    invOL2 : ((OpRegularSemigroupTerm2 n A )  → (OpRegularSemigroupTerm2 n A ) ) 
  
  simplifyB : (RegularSemigroupTerm  → RegularSemigroupTerm )
  simplifyB (opL x1 x2 )  = (opL (simplifyB x1 ) (simplifyB x2 ) )
  
  simplifyB (invL x1 )  = (invL (simplifyB x1 ) )
  
  simplifyCl : ((A  : Set )  → ((ClRegularSemigroupTerm A ) → (ClRegularSemigroupTerm A )))
  simplifyCl _ (opCl x1 x2 )  = (opCl (simplifyCl _ x1 ) (simplifyCl _ x2 ) )
  
  simplifyCl _ (invCl x1 )  = (invCl (simplifyCl _ x1 ) )
  
  simplifyCl _ (sing x1 )  = (sing x1 )
  
  simplifyOp : ((n  : Nat)  → ((OpRegularSemigroupTerm n ) → (OpRegularSemigroupTerm n )))
  simplifyOp _ (opOL x1 x2 )  = (opOL (simplifyOp _ x1 ) (simplifyOp _ x2 ) )
  
  simplifyOp _ (invOL x1 )  = (invOL (simplifyOp _ x1 ) )
  
  simplifyOp _ (v x1 )  = (v x1 )
  
  simplifyOpE : ((n  : Nat ) (A  : Set )  → ((OpRegularSemigroupTerm2 n A ) → (OpRegularSemigroupTerm2 n A )))
  simplifyOpE _ _ (opOL2 x1 x2 )  = (opOL2 (simplifyOpE _ _ x1 ) (simplifyOpE _ _ x2 ) )
  
  simplifyOpE _ _ (invOL2 x1 )  = (invOL2 (simplifyOpE _ _ x1 ) )
  
  simplifyOpE _ _ (v2 x1 )  = (v2 x1 )
  
  simplifyOpE _ _ (sing2 x1 )  = (sing2 x1 )
  
  evalB : ({A  : Set }  → ((RegularSemigroup A ) → (RegularSemigroupTerm  → A )))
  evalB Re (opL x1 x2 )  = ((op Re ) (evalB Re x1 ) (evalB Re x2 ) )
  
  evalB Re (invL x1 )  = ((inv Re ) (evalB Re x1 ) )
  
  evalCl : ({A  : Set }  → ((RegularSemigroup A ) → ((ClRegularSemigroupTerm A ) → A )))
  evalCl Re (sing x1 )  = x1 
  
  evalCl Re (opCl x1 x2 )  = ((op Re ) (evalCl Re x1 ) (evalCl Re x2 ) )
  
  evalCl Re (invCl x1 )  = ((inv Re ) (evalCl Re x1 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((RegularSemigroup A ) → ((Vec A n ) → ((OpRegularSemigroupTerm n ) → A ))))
  evalOp n Re vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Re vars (opOL x1 x2 )  = ((op Re ) (evalOp n Re vars x1 ) (evalOp n Re vars x2 ) )
  
  evalOp n Re vars (invOL x1 )  = ((inv Re ) (evalOp n Re vars x1 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((RegularSemigroup A ) → ((Vec A n ) → ((OpRegularSemigroupTerm2 n A ) → A ))))
  evalOpE n Re vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Re vars (sing2 x1 )  = x1 
  
  evalOpE n Re vars (opOL2 x1 x2 )  = ((op Re ) (evalOpE n Re vars x1 ) (evalOpE n Re vars x2 ) )
  
  evalOpE n Re vars (invOL2 x1 )  = ((inv Re ) (evalOpE n Re vars x1 ) )
  
  inductionB : ((P  : (RegularSemigroupTerm  → Set ))  → (((x1 x2  : RegularSemigroupTerm  )  → ((P x1 ) → ((P x2 ) → (P (opL x1 x2 ) )))) → (((x1  : RegularSemigroupTerm  )  → ((P x1 ) → (P (invL x1 ) ))) → ((x  : RegularSemigroupTerm )  → (P x )))))
  inductionB p popl pinvl (opL x1 x2 )  = (popl _ _ (inductionB p popl pinvl x1 ) (inductionB p popl pinvl x2 ) )
  
  inductionB p popl pinvl (invL x1 )  = (pinvl _ (inductionB p popl pinvl x1 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClRegularSemigroupTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClRegularSemigroupTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (opCl x1 x2 ) )))) → (((x1  : (ClRegularSemigroupTerm A ) )  → ((P x1 ) → (P (invCl x1 ) ))) → ((x  : (ClRegularSemigroupTerm A ))  → (P x ))))))
  inductionCl _ p psing popcl pinvcl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing popcl pinvcl (opCl x1 x2 )  = (popcl _ _ (inductionCl _ p psing popcl pinvcl x1 ) (inductionCl _ p psing popcl pinvcl x2 ) )
  
  inductionCl _ p psing popcl pinvcl (invCl x1 )  = (pinvcl _ (inductionCl _ p psing popcl pinvcl x1 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpRegularSemigroupTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpRegularSemigroupTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (opOL x1 x2 ) )))) → (((x1  : (OpRegularSemigroupTerm n ) )  → ((P x1 ) → (P (invOL x1 ) ))) → ((x  : (OpRegularSemigroupTerm n ))  → (P x ))))))
  inductionOp _ p pv popol pinvol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv popol pinvol (opOL x1 x2 )  = (popol _ _ (inductionOp _ p pv popol pinvol x1 ) (inductionOp _ p pv popol pinvol x2 ) )
  
  inductionOp _ p pv popol pinvol (invOL x1 )  = (pinvol _ (inductionOp _ p pv popol pinvol x1 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpRegularSemigroupTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpRegularSemigroupTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (opOL2 x1 x2 ) )))) → (((x1  : (OpRegularSemigroupTerm2 n A ) )  → ((P x1 ) → (P (invOL2 x1 ) ))) → ((x  : (OpRegularSemigroupTerm2 n A ))  → (P x )))))))
  inductionOpE _ _ p pv2 psing2 popol2 pinvol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 pinvol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 popol2 pinvol2 (opOL2 x1 x2 )  = (popol2 _ _ (inductionOpE _ _ p pv2 psing2 popol2 pinvol2 x1 ) (inductionOpE _ _ p pv2 psing2 popol2 pinvol2 x2 ) )
  
  inductionOpE _ _ p pv2 psing2 popol2 pinvol2 (invOL2 x1 )  = (pinvol2 _ (inductionOpE _ _ p pv2 psing2 popol2 pinvol2 x1 ) )
  
  opL' : (  (RegularSemigroupTerm   → (RegularSemigroupTerm   → RegularSemigroupTerm  )))
  opL' x1 x2  = (opL x1 x2 )
  
  invL' : (  (RegularSemigroupTerm   → RegularSemigroupTerm  ))
  invL' x1  = (invL x1 )
  
  stageB : (RegularSemigroupTerm  → (Staged RegularSemigroupTerm  ))
  stageB (opL x1 x2 )  = (stage2 opL' (codeLift2 opL' ) (stageB  x1 ) (stageB  x2 ) )
  
  stageB (invL x1 )  = (stage1 invL' (codeLift1 invL' ) (stageB  x1 ) )
  
  opCl' : ({A  : Set }  → ((ClRegularSemigroupTerm A )  → ((ClRegularSemigroupTerm A )  → (ClRegularSemigroupTerm A ) )))
  opCl' x1 x2  = (opCl x1 x2 )
  
  invCl' : ({A  : Set }  → ((ClRegularSemigroupTerm A )  → (ClRegularSemigroupTerm A ) ))
  invCl' x1  = (invCl x1 )
  
  stageCl : ((A  : Set )  → ((ClRegularSemigroupTerm A ) → (Staged (ClRegularSemigroupTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (opCl x1 x2 )  = (stage2 opCl' (codeLift2 opCl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  stageCl _ (invCl x1 )  = (stage1 invCl' (codeLift1 invCl' ) ((stageCl _ ) x1 ) )
  
  opOL' : ({n  : Nat}  → ((OpRegularSemigroupTerm n )  → ((OpRegularSemigroupTerm n )  → (OpRegularSemigroupTerm n ) )))
  opOL' x1 x2  = (opOL x1 x2 )
  
  invOL' : ({n  : Nat}  → ((OpRegularSemigroupTerm n )  → (OpRegularSemigroupTerm n ) ))
  invOL' x1  = (invOL x1 )
  
  stageOp : ((n  : Nat)  → ((OpRegularSemigroupTerm n ) → (Staged (OpRegularSemigroupTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (opOL x1 x2 )  = (stage2 opOL' (codeLift2 opOL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  stageOp _ (invOL x1 )  = (stage1 invOL' (codeLift1 invOL' ) ((stageOp _ ) x1 ) )
  
  opOL2' : ({n  : Nat } {A  : Set }  → ((OpRegularSemigroupTerm2 n A )  → ((OpRegularSemigroupTerm2 n A )  → (OpRegularSemigroupTerm2 n A ) )))
  opOL2' x1 x2  = (opOL2 x1 x2 )
  
  invOL2' : ({n  : Nat } {A  : Set }  → ((OpRegularSemigroupTerm2 n A )  → (OpRegularSemigroupTerm2 n A ) ))
  invOL2' x1  = (invOL2 x1 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpRegularSemigroupTerm2 n A ) → (Staged (OpRegularSemigroupTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (opOL2 x1 x2 )  = (stage2 opOL2' (codeLift2 opOL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  stageOpE _ _ (invOL2 x1 )  = (stage1 invOL2' (codeLift1 invOL2' ) ((stageOpE _ _ ) x1 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      opT : ((Repr A )  → ((Repr A )  → (Repr A ) ))
      invT : ((Repr A )  → (Repr A ) ) 
   
