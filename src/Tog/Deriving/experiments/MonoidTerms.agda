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

data Comp (A : Set) : Set where
  Computation : Choice → Code A → Comp A

-- T from a term to its code 
data Staged (A : Set) : Set where
  Now : A → Staged A 
  Later : Code A → Staged A

data MonTerm : Set where
  e' : MonTerm
  op' : MonTerm → MonTerm → MonTerm

induction : (P : MonTerm → Set) → P e' → ((x y : MonTerm) → P x → P y → P (op' x y)) → ((x : MonTerm) → P x)
induction p pe _ e' = pe
induction p pe f (op' e1 e2) = f _ _ (induction p pe f e1) (induction p pe f e2)

liftUnary : {A B : Set} → (A → B) → (Code A → Code B) → Staged A → Staged B
liftUnary f g (Now x) = Now (f x)
liftUnary f g (Later x) = Later (g x)


{-
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


record MonoidStaged (A : Set) (T : Set → Set) : Set where
 field
  e'  : Staged A T
  op' : Staged A T → Staged A T → Staged A T

record Symantics {A : Set} (rep : Set → Set) (M : Monoid A) : Set₁ where
  field
   Id : rep A
   _⨾_ : rep A → rep A → rep A 



record LiftMon (A : Set) : Set where
  eS : Staged MonTerm
  opS : ?


data MonSt : Set where
  e' : Staged MonTerm Code → MonSt
  op' : Staged MonTerm Code → Staged MonTerm Code → Staged MonTerm Code → MonSt

exp1 : Staged MonTerm Code 
exp1 = Later (Computation Expr (Q (Q (op' e' e'))))-- (op' (Now e') (Now e')))

exp2 : MonSt
exp2 = e' (Now e') 
-}
{-



Later op (Now e) (Now e) 


record Repr (A : Set) (T : Set → Set) : Set where
  field
   now : Maybe A
   later : Π Comp (T A) 
-}


{-
eval : MonTerm ℕ → ℕ 
eval e' = zero
eval (op' x₁ x₂) = (eval x₁) + (eval x₂)


monterm : MonTerm ℕ
monterm = op' (op' e' (op' e' e')) (op' e' e')

f : Set → Set
f x = Code x 
-}
--stMonterm : Staged (MonTerm ℕ) f 
--stMonterm = Later (Computation Expr (Q (Q e ))) 
-- correct: stMonterm = Later (Computation Expr (Q (op' e' e')))
-- correct: stMonterm = Later (Computation Expr (Q e'))
-- wrong: Later (Computation Expr (Q (c monterm)))  -- Now monterm 




{-
(Now e) (Now e1) -> Now (op e e1)
(Later x) (Now y) -> Later (op x (quote y))
Staged :: Term A -> A -> Set
Staged :: (Set -> Set) -> Set -> Set
data .. Now | Later
record { Now :: Maybe A; Later :: Term A }
A + B
(1 + A) * B = 1B + AB
= B + A*B
-}
{-
expp : Code (MonTerm ℕ) → Staged (MonTerm ℕ)
expp = op Now (op' (Now e') (Now e')) -- Later (Computation Expression (Q (op' e' e')))
-}

data MonOpenTerm (n : ℕ) : Set where
  v  : Fin n → MonOpenTerm n 
  e  : MonOpenTerm n
  op : MonOpenTerm n → MonOpenTerm n → MonOpenTerm n

-- lifting unary function
{- 


-- Evaluator (interpreter) 
eval : {A : Set} {n : ℕ} → MonOpenTerm n → Vec A n → A
eval = {!!}

-- Simplification rules

-- Partial evaluator
peval : {!!}
peval = {!!}
-}
{-
record MonTermStaged {A : Set} : Set where
 field
  eStaged  : Staged A 
  opStaged : Staged A → Staged A → Staged A
-}
{- 
liftMonTerm : MonTerm → Code MonTerm → Staged MonTerm
liftMonTerm e code = Now e
liftMonTerm (op x y) code = liftBinary op code (Now x) (Now y)
-} 

-- Finally Tagless 
