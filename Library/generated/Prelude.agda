module Prelude where
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Data.Fin
open import Data.Vec
record Prod (A B  : Set )  : Set where
  constructor prodC
  field
    fst : A 
    snd : B  

data Wrap (A  : Set )  : Set where
  Q : (A  → (Wrap A )) 

data Stage  : Set where
  s0 : Stage 
  s1 : Stage  

CodeRep : ((A  : Set ) (s  : Stage )  → Set )
CodeRep A s0  = A 

CodeRep A s1  = (Wrap (CodeRep A s0 ) )

uncode : ({A  : Set }  → ((CodeRep A s1 ) → (CodeRep A s0 )))
uncode (Q x )  = x 

code : ({A  : Set }  → ((CodeRep A s0 ) → (CodeRep A s1 )))
code x  = (Q x )

run : ({A  : Set }  → ((CodeRep A s1 ) → A ))
run (Q x )  = x 

data Choice  : Set where
  Expr : Choice 
  Const : Choice  

data Comp (A  : Set ) (s  : Stage )  : Set where
  Computation : (Choice  → ((CodeRep A s ) → (Comp A s ))) 

data Staged (A  : Set )  : Set where
  Now : (A  → (Staged A ))
  Later : ((Comp A s1 ) → (Staged A )) 

expr : ({A  : Set }  → ((CodeRep A s1 ) → (Staged A )))
expr x  = (Later (Computation Expr x ) )

const : ({A  : Set }  → ((CodeRep A s1 ) → (Staged A )))
const x  = (Later (Computation Const x ) )

stage0 : ({A  : Set }  → (A  → (Staged A )))
stage0 x  = (Now x )

stage1 : ({A B  : Set }  → ((A  → B )  → (((CodeRep A s1 ) → (CodeRep B s1 ))  → ((Staged A ) → (Staged B )))))
stage1 f g (Now x )  = (Now (f x ) )

stage1 f g (Later (Computation _ x ) )  = (expr (g x ) )

stage2 : ({A B C  : Set }  → ((A  → (B  → C ))  → (((CodeRep A s1 ) → ((CodeRep B s1 ) → (CodeRep C s1 )))  → ((Staged A ) → ((Staged B ) → (Staged C ))))))
stage2 f _ (Now x ) (Now y )  = (stage0 (f x y ) )

stage2 _ g (Now x ) (Later (Computation _ y ) )  = (expr (g (code x ) y ) )

stage2 _ g (Later (Computation _ x ) ) (Now y )  = (expr (g x (code y ) ) )

stage2 _ g (Later (Computation _ x ) ) (Later (Computation _ y ) )  = (expr (g x y ) )

codeLift1 : ({A B  : Set }  → ((A  → B )  → ((CodeRep A s1 ) → (CodeRep B s1 )) ))
codeLift1 f (Q x )  = (Q (f x ) )

codeLift2 : ({A B C  : Set }  → ((A  → (B  → C ))  → ((CodeRep A s1 ) → ((CodeRep B s1 ) → (CodeRep C s1 ))) ))
codeLift2 f (Q x ) (Q y )  = (Q (f x y ) )
