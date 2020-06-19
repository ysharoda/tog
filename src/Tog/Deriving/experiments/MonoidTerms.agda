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
  Expr  : Choice
  Const : Choice

data Code (A : Set) : Set where
  Q : A → Code A

uncode : {A : Set} -> Code A -> A
uncode (Q x) = x

data Comp (A : Set) : Set where
  Computation : Choice → Code A → Comp A

-- T from a term to its code 
data Staged (A : Set) : Set where
  Now : A → Staged A 
  Later : Comp A → Staged A

data MonTerm : Set where
  e' : MonTerm
  op' : MonTerm → MonTerm → MonTerm

eCode : Code MonTerm
eCode = Q (e')

opCode : (MonTerm -> MonTerm -> MonTerm) -> Code MonTerm -> Code MonTerm -> Code MonTerm
opCode f x y = Q (f (uncode x) (uncode y)) 

induction : (P : MonTerm → Set) → P e' → ((x y : MonTerm) → P x → P y → P (op' x y)) → ((x : MonTerm) → P x)
induction p pe _ e' = pe
induction p pe f (op' e1 e2) = f _ _ (induction p pe f e1) (induction p pe f e2)

liftConstant : {A : Set} -> A -> Staged A
liftConstant x = Now x

liftUnary : {A B : Set} → (A → B) → Staged A → Staged B
liftUnary f (Now x) = Now (f x)
liftUnary f (Later (Computation _ x)) = Later (Computation Expr (Q (f (uncode x))))

liftBinary : {A B C : Set} -> (A -> B -> C) ->
                              (Code A -> Code B -> Code C) ->
                               Staged A -> Staged B -> Staged C
liftBinary f g (Now x) (Now y) = Now (f x y)
liftBinary f g (Now x) (Later (Computation _ y)) =
  Later (Computation Expr (g (Q x) y))
liftBinary f g (Later (Computation _ x)) (Now y) =
  Later (Computation Expr (g x (Q y)))
liftBinary f g (Later (Computation _ x)) (Later (Computation _ y)) =
  Later (Computation Expr (g x y))

liftMonExpr : MonTerm -> Staged MonTerm
liftMonExpr e' = liftConstant e'
liftMonExpr (op' x y) =
  liftBinary (op') (opCode (op')) (liftMonExpr x) (liftMonExpr y)

record MonoidTagless (A : Set) (Repr : Set -> Set) : Set where
 field 
   e : Repr A
   op : Repr A -> Repr A -> Repr A
