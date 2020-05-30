module MonoidTerms where

open import Relation.Binary.PropositionalEquality

record Monoid (A : Set) : Set where
 field
   e : A
   op : A → A → A
   lunit : {x : A} → op e x ≡ x
   runit : {x : A} → op x e ≡ x
   assoc : {x y z : A} → op x (op y z) ≡ op (op x y) z 
                                                      
data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (succ n)
  fsucc : {n : Nat} → Fin n → Fin (succ n) 

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

data MonOpenTerm : Set where
  v  : {n : Nat} → Fin n → MonOpenTerm
  e  : MonOpenTerm
  op : MonOpenTerm → MonOpenTerm → MonOpenTerm 

data MonoidPE : Set where
  e  : Staged MonTerm → MonoidPE
  op : Staged MonTerm → Staged MonTerm → Staged MonTerm → MonoidPE

-- lifting unary function
liftUnary : {A B : Set} → (A → B) → Staged A → Staged B
liftUnary f (Now x) = Now (f x)
liftUnary f (Later x) = Later (Computation Expression {!!})
