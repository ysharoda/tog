module IdempotentAdditiveMagma  where
  open import Prelude
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Data.Fin
  open import Data.Vec
  record IdempotentAdditiveMagma (A  : Set )  : Set where
    constructor IdempotentAdditiveMagmaC
    field
      + : (A  → (A  → A ))
      idempotent_+ : ({x  : A }  → (+ x x ) ≡ x )
  open IdempotentAdditiveMagma
  record Sig (AS  : Set )  : Set where
    constructor SigSigC
    field
      +S : (AS  → (AS  → AS ))
  record Product (AP  : Set )  : Set where
    constructor ProductC
    field
      +P : ((Prod AP AP ) → ((Prod AP AP ) → (Prod AP AP )))
      idempotent_+P : ({xP  : (Prod AP AP )}  → (+P xP xP ) ≡ xP )
  record Hom (A1 A2  : Set ) (Id1  : (IdempotentAdditiveMagma A1 )) (Id2  : (IdempotentAdditiveMagma A2 ))  : Set where
    constructor HomC
    field
      hom : (A1 → A2)
      pres-+ : ({x1  : A1} {x2  : A1}  → (hom ((+ Id1 ) x1 x2 ) ) ≡ ((+ Id2 ) (hom x1 ) (hom x2 ) ))
  record RelInterp (A1 A2  : Set ) (Id1  : (IdempotentAdditiveMagma A1 )) (Id2  : (IdempotentAdditiveMagma A2 ))  : Set₁ where
    constructor RelInterpC
    field
      interp : (A1 → (A2 → Set))
      interp-+ : ({x1  : A1} {x2  : A1} {y1  : A2} {y2  : A2}  → ((interp x1 y1 ) → ((interp x2 y2 ) → (interp ((+ Id1 ) x1 x2 ) ((+ Id2 ) y1 y2 ) ))))
  data IdempotentAdditiveMagmaTerm  : Set where
    +L : (IdempotentAdditiveMagmaTerm   → (IdempotentAdditiveMagmaTerm   → IdempotentAdditiveMagmaTerm  ))
  data ClIdempotentAdditiveMagmaTerm (A  : Set )  : Set where
    sing : (A  → (ClIdempotentAdditiveMagmaTerm A ) )
    +Cl : ((ClIdempotentAdditiveMagmaTerm A )  → ((ClIdempotentAdditiveMagmaTerm A )  → (ClIdempotentAdditiveMagmaTerm A ) ))
  data OpIdempotentAdditiveMagmaTerm (n  : Nat)  : Set where
    v : ((Fin n ) → (OpIdempotentAdditiveMagmaTerm n ) )
    +OL : ((OpIdempotentAdditiveMagmaTerm n )  → ((OpIdempotentAdditiveMagmaTerm n )  → (OpIdempotentAdditiveMagmaTerm n ) ))
  data OpIdempotentAdditiveMagmaTerm2 (n  : Nat ) (A  : Set )  : Set where
    v2 : ((Fin n ) → (OpIdempotentAdditiveMagmaTerm2 n A ) )
    sing2 : (A  → (OpIdempotentAdditiveMagmaTerm2 n A ) )
    +OL2 : ((OpIdempotentAdditiveMagmaTerm2 n A )  → ((OpIdempotentAdditiveMagmaTerm2 n A )  → (OpIdempotentAdditiveMagmaTerm2 n A ) ))
  evalB : ({A  : Set }  → ((IdempotentAdditiveMagma A ) → (IdempotentAdditiveMagmaTerm  → A )))
  evalB Id (+L x1 x2 )  = ((+ Id ) (evalB Id x1 ) (evalB Id x2 ) )
  
  evalCl : ({A  : Set }  → ((IdempotentAdditiveMagma A ) → ((ClIdempotentAdditiveMagmaTerm A ) → A )))
  evalCl Id (sing x1 )  = x1 
  
  evalCl Id (+Cl x1 x2 )  = ((+ Id ) (evalCl Id x1 ) (evalCl Id x2 ) )
  
  evalOp : ({A  : Set } (n  : Nat)  → ((IdempotentAdditiveMagma A ) → ((Vec A n ) → ((OpIdempotentAdditiveMagmaTerm n ) → A ))))
  evalOp n Id vars (v x1 )  = (lookup vars x1 )
  
  evalOp n Id vars (+OL x1 x2 )  = ((+ Id ) (evalOp n Id vars x1 ) (evalOp n Id vars x2 ) )
  
  evalOpE : ({A  : Set } (n  : Nat )  → ((IdempotentAdditiveMagma A ) → ((Vec A n ) → ((OpIdempotentAdditiveMagmaTerm2 n A ) → A ))))
  evalOpE n Id vars (v2 x1 )  = (lookup vars x1 )
  
  evalOpE n Id vars (sing2 x1 )  = x1 
  
  evalOpE n Id vars (+OL2 x1 x2 )  = ((+ Id ) (evalOpE n Id vars x1 ) (evalOpE n Id vars x2 ) )
  
  inductionB : ((P  : (IdempotentAdditiveMagmaTerm  → Set ))  → (((x1 x2  : IdempotentAdditiveMagmaTerm  )  → ((P x1 ) → ((P x2 ) → (P (+L x1 x2 ) )))) → ((x  : IdempotentAdditiveMagmaTerm )  → (P x ))))
  inductionB p p+l (+L x1 x2 )  = (p+l _ _ (inductionB p p+l x1 ) (inductionB p p+l x2 ) )
  
  inductionCl : ((A  : Set ) (P  : ((ClIdempotentAdditiveMagmaTerm A ) → Set ))  → (((x1  : A )  → (P (sing x1 ) )) → (((x1 x2  : (ClIdempotentAdditiveMagmaTerm A ) )  → ((P x1 ) → ((P x2 ) → (P (+Cl x1 x2 ) )))) → ((x  : (ClIdempotentAdditiveMagmaTerm A ))  → (P x )))))
  inductionCl _ p psing p+cl (sing x1 )  = (psing x1 )
  
  inductionCl _ p psing p+cl (+Cl x1 x2 )  = (p+cl _ _ (inductionCl _ p psing p+cl x1 ) (inductionCl _ p psing p+cl x2 ) )
  
  inductionOp : ((n  : Nat) (P  : ((OpIdempotentAdditiveMagmaTerm n ) → Set ))  → (((fin  : (Fin n ))  → (P (v fin ) )) → (((x1 x2  : (OpIdempotentAdditiveMagmaTerm n ) )  → ((P x1 ) → ((P x2 ) → (P (+OL x1 x2 ) )))) → ((x  : (OpIdempotentAdditiveMagmaTerm n ))  → (P x )))))
  inductionOp _ p pv p+ol (v x1 )  = (pv x1 )
  
  inductionOp _ p pv p+ol (+OL x1 x2 )  = (p+ol _ _ (inductionOp _ p pv p+ol x1 ) (inductionOp _ p pv p+ol x2 ) )
  
  inductionOpE : ((n  : Nat ) (A  : Set ) (P  : ((OpIdempotentAdditiveMagmaTerm2 n A ) → Set ))  → (((fin  : (Fin n ))  → (P (v2 fin ) )) → (((x1  : A )  → (P (sing2 x1 ) )) → (((x1 x2  : (OpIdempotentAdditiveMagmaTerm2 n A ) )  → ((P x1 ) → ((P x2 ) → (P (+OL2 x1 x2 ) )))) → ((x  : (OpIdempotentAdditiveMagmaTerm2 n A ))  → (P x ))))))
  inductionOpE _ _ p pv2 psing2 p+ol2 (v2 x1 )  = (pv2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (sing2 x1 )  = (psing2 x1 )
  
  inductionOpE _ _ p pv2 psing2 p+ol2 (+OL2 x1 x2 )  = (p+ol2 _ _ (inductionOpE _ _ p pv2 psing2 p+ol2 x1 ) (inductionOpE _ _ p pv2 psing2 p+ol2 x2 ) )
  
  +L' : (  (IdempotentAdditiveMagmaTerm   → (IdempotentAdditiveMagmaTerm   → IdempotentAdditiveMagmaTerm  )))
  +L' x1 x2  = (+L x1 x2 )
  
  stageB : (IdempotentAdditiveMagmaTerm  → (Staged IdempotentAdditiveMagmaTerm  ))
  stageB (+L x1 x2 )  = (stage2 +L' (codeLift2 +L' ) (stageB  x1 ) (stageB  x2 ) )
  
  +Cl' : ({A  : Set }  → ((ClIdempotentAdditiveMagmaTerm A )  → ((ClIdempotentAdditiveMagmaTerm A )  → (ClIdempotentAdditiveMagmaTerm A ) )))
  +Cl' x1 x2  = (+Cl x1 x2 )
  
  stageCl : ((A  : Set )  → ((ClIdempotentAdditiveMagmaTerm A ) → (Staged (ClIdempotentAdditiveMagmaTerm A ) )))
  stageCl _ (sing x1 )  = (Now (sing x1 ) )
  
  stageCl _ (+Cl x1 x2 )  = (stage2 +Cl' (codeLift2 +Cl' ) ((stageCl _ ) x1 ) ((stageCl _ ) x2 ) )
  
  +OL' : ({n  : Nat}  → ((OpIdempotentAdditiveMagmaTerm n )  → ((OpIdempotentAdditiveMagmaTerm n )  → (OpIdempotentAdditiveMagmaTerm n ) )))
  +OL' x1 x2  = (+OL x1 x2 )
  
  stageOp : ((n  : Nat)  → ((OpIdempotentAdditiveMagmaTerm n ) → (Staged (OpIdempotentAdditiveMagmaTerm n ) )))
  stageOp _ (v x1 )  = (const (code (v x1 ) ) )
  
  stageOp _ (+OL x1 x2 )  = (stage2 +OL' (codeLift2 +OL' ) ((stageOp _ ) x1 ) ((stageOp _ ) x2 ) )
  
  +OL2' : ({n  : Nat } {A  : Set }  → ((OpIdempotentAdditiveMagmaTerm2 n A )  → ((OpIdempotentAdditiveMagmaTerm2 n A )  → (OpIdempotentAdditiveMagmaTerm2 n A ) )))
  +OL2' x1 x2  = (+OL2 x1 x2 )
  
  stageOpE : ((n  : Nat ) (A  : Set )  → ((OpIdempotentAdditiveMagmaTerm2 n A ) → (Staged (OpIdempotentAdditiveMagmaTerm2 n A ) )))
  stageOpE _ _ (sing2 x1 )  = (Now (sing2 x1 ) )
  
  stageOpE _ _ (v2 x1 )  = (const (code (v2 x1 ) ) )
  
  stageOpE _ _ (+OL2 x1 x2 )  = (stage2 +OL2' (codeLift2 +OL2' ) ((stageOpE _ _ ) x1 ) ((stageOpE _ _ ) x2 ) )
  
  record Tagless (A  : Set) (Repr  : (Set  → Set ))  : Set where
    constructor tagless
    field
      +T : ((Repr A )  → ((Repr A )  → (Repr A ) ))