module MonoidTerms where

open import Relation.Binary.PropositionalEquality
open import Data.Vec.Base using (Vec; lookup)
open import Data.Nat.Base

record Monoid (A : Set) : Set where
 field
   e : A
   op : A → A → A
   lunit : {x : A} → op e x ≡ x
   runit : {x : A} → op x e ≡ x
   assoc : {x y z : A} → op x (op y z) ≡ op (op x y) z 
                                                      
data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsucc : {n : ℕ} → Fin n → Fin (suc n) 

data Choice : Set where
  Expression : Choice
  Constant : Choice

data Code (A : Set) : Set where
  Q : A → Code A 

data Comp (A : Set) : Set where
  Computation : Choice → Code A → Comp A

data Staged (A : Set) : Set where
  Now : A → Staged A
  Later : Comp A → Staged A

data MonTerm : Set where
  e  : MonTerm
  op : MonTerm → MonTerm → MonTerm

data MonOpenTerm (n : ℕ) : Set where
  v  : Fin n → MonOpenTerm n 
  e  : MonOpenTerm n
  op : MonOpenTerm n → MonOpenTerm n → MonOpenTerm n

-- lifting unary function
liftUnary : {A B : Set} → (A → B) → (Code A → Code B) → Staged A → Staged B
liftUnary f _ (Now x) = Now (f x)
liftUnary f g (Later (Computation _ x)) = Later (Computation Expression (g x))


liftBinary : {A B C : Set} -> (A -> B -> C) ->
                              (Code A -> Code B -> Code C) ->
                               Staged A -> Staged B -> Staged C
liftBinary f g (Now x) (Now y) = Now (f x y)
liftBinary f g (Now x) (Later (Computation _ y)) =
  Later (Computation Expression (g (Q x) y))
liftBinary f g (Later (Computation _ x)) (Now y) =
  Later (Computation Expression (g x (Q y)))
liftBinary f g (Later (Computation _ x)) (Later (Computation _ y)) =
  Later (Computation Expression (g x y))

-- Evaluator (interpreter) 
eval : {A : Set} {n : ℕ} → MonOpenTerm n → Vec A n → A
eval = {!!}

-- Simplification rules

-- Partial evaluator
peval : {!!}
peval = {!!}

{- 
liftMonTerm : MonTerm → Code MonTerm → Staged MonTerm
liftMonTerm e code = Now e
liftMonTerm (op x y) code = liftBinary op code (Now x) (Now y)
-} 

record MonTermStaged {A : Set} : Set where
 field
  eStaged  : Staged A 
  opStaged : Staged A → Staged A → Staged A

-- Finally Tagless 
