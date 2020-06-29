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

-- Even though we eventually want to do multi-staged programming, most code
-- only uses 2 levels, so hardwire that simplifying assumption here.

module Code where
  data Wrap (A : Set) : Set where
    Q : A → Wrap A

  data Stage : Set where s0 s1 : Stage

  CodeRep : (A : Set) (s : Stage) → Set
  CodeRep A s0 = A
  CodeRep A s1 = Wrap (CodeRep A s0)

  uncode : {A : Set} → CodeRep A s1 → CodeRep A s0
  uncode (Q x) = x

  code : {A : Set} → CodeRep A s0 → CodeRep A s1
  code = Q

  run : {A : Set} → CodeRep A s1 → A
  run (Q x) = x

  splice = uncode

module Staged where
  open Code

  data Choice : Set where
    Expr  : Choice
    Const : Choice

  data Comp (A : Set) (s : Stage) : Set where
    Computation : Choice → CodeRep A s → Comp A s

  data Staged (A : Set) : Set where
    Now : A → Staged A
    Later : Comp A s1 → Staged A

  expr : {A : Set} → CodeRep A s1 → Staged A
  expr x = Later (Computation Expr x)

  const : {A : Set} → CodeRep A s1 → Staged A
  const x = Later (Computation Const x)

  stage0 : {A : Set} -> A -> Staged A
  stage0 = Now

  stage1 : {A B : Set} → (A → B) → (CodeRep A s1 → CodeRep B s1) → Staged A → Staged B
  stage1 f g (Now x)                   = Now (f x)
  stage1 f g (Later (Computation _ x)) = expr (g x)

  pattern pconst x = Later (Computation Const x)
  pattern pcode x  = Later (Computation _ x)

  stage2 : {A B C : Set} -> (A -> B -> C) -> (CodeRep A s1 → CodeRep B s1 → CodeRep C s1) →
    Staged A -> Staged B -> Staged C
  stage2 f _ (Now x)   (Now y)   = stage0 (f x y)
  stage2 _ g (Now x)   (pcode y) = expr (g (code x) y)
  stage2 _ g (pcode x) (Now y)   = expr (g x (code y))
  stage2 _ g (pcode x) (pcode y) = expr (g x y)

  -- this is kind of cheating... but we don't have true staging
  codeLift : {A B C : Set} → (f : A → B → C) → CodeRep A s1 → CodeRep B s1 → CodeRep C s1
  codeLift f (Q x) (Q y) = Q (f x y)

open Code
open Staged

data MonTerm : Set where
  e' : MonTerm
  op' : MonTerm → MonTerm → MonTerm

induction : (P : MonTerm → Set) → P e' → ({x y : MonTerm} → P x → P y → P (op' x y)) → ((x : MonTerm) → P x)
induction p pe _ e'          = pe
induction p pe f (op' e1 e2) = f (induction p pe f e1) (induction p pe f e2)

data OpenMonTerm (n : ℕ) : Set where
  v  : Fin n → OpenMonTerm n
  e' : OpenMonTerm n
  op' : OpenMonTerm n → OpenMonTerm n → OpenMonTerm n

-- This is trivial, because the input is static!
liftMonExpr : MonTerm -> Staged MonTerm
liftMonExpr x = Now x

-- This is non-trivial as variables are dynamic
liftOpenMonExpr : {n : ℕ} → OpenMonTerm n -> Staged (OpenMonTerm n)
liftOpenMonExpr (v fin)   = const (code (v fin))
liftOpenMonExpr e'        = Now e'
liftOpenMonExpr (op' x y) = stage2 op' (codeLift op') (liftOpenMonExpr x) (liftOpenMonExpr y)

record MonoidTagless (A : Set) (Repr : Set -> Set) : Set where
 field
   e : Repr A
   op : Repr A -> Repr A -> Repr A

record MonoidTagless2 (Repr : Set -> Set) : Set₁ where
  field
    A : Set
    e : Repr A
    op : Repr A -> Repr A -> Repr A
