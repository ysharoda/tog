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
   data CodeRep (A : Set) (n : ℕ) : Set where
     Q : A → CodeRep A n

   uncode : {n : ℕ} {A : Set} → CodeRep A (suc n) → CodeRep A n
   uncode (Q x) = Q x

   run : {A : Set} → CodeRep A zero → A
   run (Q x) = x

   splice = uncode

   code :  {A : Set} → A → CodeRep A zero
   code x = Q x

   push-code : {n : ℕ} {A : Set} → CodeRep A n -> CodeRep A (suc n)
   push-code (Q x) = Q x

module Staged where
  open Code

  data Choice : Set where
    Expr  : Choice
    Const : Choice

  data Comp (A : Set) (n : ℕ) : Set where
    Computation : Choice → CodeRep A n → Comp A n

  code1 : {A B : Set} → (A → B) → (CodeRep A zero → CodeRep B zero)
  code1 f x = code (f (run x))

  code2 : {A B C : Set} → (A → B → C) → (CodeRep A zero → CodeRep B zero → CodeRep C zero)
  code2 f x y = code (f (run x) (run y))

  data Staged (A : Set) : (n : ℕ) → Set where
    Now : A → Staged A zero
    Later : ∀ {n} → Comp A n → Staged A n

  expr : {A : Set} {n : ℕ} → CodeRep A n → Staged A n
  expr x = Later (Computation Expr x)

  const : {A : Set} {n : ℕ} → CodeRep A n → Staged A n
  const x = Later (Computation Const x)

  stage0 : {A : Set} -> A -> Staged A zero
  stage0 = Now

  stage1 : {A B : Set} → (A → B) → Staged A zero → Staged B zero
  stage1 f (Now x) = Now (f x)
  stage1 f (Later (Computation _ x)) = expr (code1 f x)

  pattern pconst x = Later (Computation Const x)
  pattern pcode x  = Later (Computation _ x)

  stage2 : {A B C : Set} -> (A -> B -> C) -> Staged A zero -> Staged B zero -> Staged C zero
  stage2 f (Now x)   (Now y)   = stage0 (f x y)
  stage2 f (Now x)   (pcode y) = expr (code2 f (code x) y)
  stage2 f (pcode x) (Now y)   = expr (code2 f x (code y))
  stage2 f (pcode x) (pcode y) = expr (code2 f x y)

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

liftMonExpr : MonTerm -> Staged MonTerm zero
-- liftMonExpr e'        = stage0 e'
-- liftMonExpr (op' x y) = stage2 op' (liftMonExpr x) (liftMonExpr y)
liftMonExpr = induction (λ _ → Staged MonTerm zero) (stage0 e') (stage2 op')

liftOpenMonExpr : {n : ℕ} → OpenMonTerm n -> Staged (OpenMonTerm n) zero
liftOpenMonExpr (v fin)   = const (code (v fin))
liftOpenMonExpr e'        = stage0 e'
liftOpenMonExpr (op' x y) = stage2 op' (liftOpenMonExpr x) (liftOpenMonExpr y)

record MonoidTagless (A : Set) (Repr : Set -> Set) : Set where
 field
   e : Repr A
   op : Repr A -> Repr A -> Repr A

record MonoidTagless2 (Repr : Set -> Set) : Set₁ where
  field
    A : Set
    e : Repr A
    op : Repr A -> Repr A -> Repr A
