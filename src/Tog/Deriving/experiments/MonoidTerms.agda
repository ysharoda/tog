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

module Code where
  abstract
   data CodeRep (A : Set) : Set where
     Q : ℕ → A → CodeRep A

   uncode : {A : Set} → CodeRep A → CodeRep A
   uncode (Q (suc s) x) = Q s x
   uncode (Q zero x) = {!!}

   run : {A : Set} → CodeRep A → A 
   run (Q zero x) = x
   run x = {!!}

   splice = uncode

   code :  {A : Set} → A → CodeRep A
   code x = Q (suc zero) x

   push-code :  {A : Set} → CodeRep A -> CodeRep A
   push-code (Q n x) = Q (suc n) x

open Code

data Choice : Set where
  Expr  : Choice
  Const : Choice

data Comp (A : Set) : Set where
  Computation : Choice → CodeRep A → Comp A

codeUnary : {A B : Set} → (A → B) → (CodeRep A → CodeRep B)
codeUnary f x = code (f (run x)) 

codeBinary : {A B C : Set} → (A → B → C) → (CodeRep A → CodeRep B → CodeRep C)
codeBinary f x y = code (f (run x) (run y))

-- T from a term to its code 
data Staged (A : Set) : Set where
  Now : A → Staged A 
  Later : Comp A → Staged A

liftConstant : {A : Set} -> A -> Staged A
liftConstant x = Now x

liftUnary : {A B : Set} → (A → B) → Staged A → Staged B
liftUnary f (Now x) = Now (f x)
liftUnary f (Later (Computation _ x)) = Later (Computation Expr (code (f (run x))))

liftBinary : {A B C : Set} -> (A -> B -> C) -> Staged A -> Staged B -> Staged C
liftBinary f (Now x) (Now y) = Now (f x y)
liftBinary f (Now x) (Later (Computation _ y)) =
  Later (Computation Expr (codeBinary f (code x) y))
liftBinary f (Later (Computation _ x)) (Now y) =
  Later (Computation Expr (codeBinary f x (code y)))
liftBinary f (Later (Computation _ x)) (Later (Computation _ y)) =
  Later (Computation Expr (codeBinary f x y))

data MonTerm : Set where
  e' : MonTerm
  op' : MonTerm → MonTerm → MonTerm

data OpenMonTerm (n : ℕ) : Set where
  v  : Fin n → OpenMonTerm n 
  e' : OpenMonTerm n
  op' : OpenMonTerm n → OpenMonTerm n → OpenMonTerm n 

liftMonExpr : MonTerm -> Staged MonTerm
liftMonExpr e' = liftConstant e'
liftMonExpr (op' x y) =
  liftBinary (op') (liftMonExpr x) (liftMonExpr y)

liftOpenMonExpr : {n : ℕ} → OpenMonTerm n -> Staged (OpenMonTerm n)
liftOpenMonExpr (v fin) = Later (Computation Const (code (v fin))) 
liftOpenMonExpr e' = liftConstant e'
liftOpenMonExpr (op' x y) =
  liftBinary (op') (liftOpenMonExpr x) (liftOpenMonExpr y)

record MonoidTagless (A : Set) (Repr : Set -> Set) : Set where
 field 
   e : Repr A
   op : Repr A -> Repr A -> Repr A

record MonoidTagless2 (Repr : Set -> Set) : Set₁ where
  field
    A : Set
    e : Repr A
    op : Repr A -> Repr A -> Repr A 

induction : (P : MonTerm → Set) → P e' → ((x y : MonTerm) → P x → P y → P (op' x y)) → ((x : MonTerm) → P x)
induction p pe _ e' = pe
induction p pe f (op' e1 e2) = f _ _ (induction p pe f e1) (induction p pe f e2)
