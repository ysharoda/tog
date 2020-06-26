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

  codeUnary : {A B : Set} → (A → B) → (CodeRep A zero → CodeRep B zero)
  codeUnary f x = code (f (run x)) 

  codeBinary : {A B C : Set} → (A → B → C) → (CodeRep A zero → CodeRep B zero → CodeRep C zero)
  codeBinary f x y = code (f (run x) (run y))

  data Staged (A : Set) (n : ℕ) : Set where
    Now : A → Staged A n -- why can't we set n to zero 
    Later : Comp A n → Staged A n

  laterExp : {A : Set} {n : ℕ} → CodeRep A n → Staged A n
  laterExp x = Later (Computation Expr x)

  laterConst : {A : Set} {n : ℕ} → CodeRep A n → Staged A n
  laterConst x = Later (Computation Const x)

  liftConstant : {A : Set} -> A -> Staged A zero 
  liftConstant x = Now x

  liftUnary : {A B : Set} → (A → B) → Staged A zero → Staged B zero
  liftUnary f (Now x) = Now (f x)
  liftUnary f (Later (Computation _ x)) = Later (Computation Expr (codeUnary f x))

  liftBinary : {A B C : Set} -> (A -> B -> C) -> Staged A zero -> Staged B zero -> Staged C zero
  liftBinary f (Now x) (Now y) = Now (f x y)
  liftBinary f (Now x) (Later (Computation _ y)) = laterExp (codeBinary f (code x) y)
  liftBinary f (Later (Computation _ x)) (Now y) = laterExp (codeBinary f x (code y))
  liftBinary f (Later (Computation _ x)) (Later (Computation _ y)) = laterExp (codeBinary f x y)

open Code 
open Staged 

data MonTerm : Set where
  e' : MonTerm
  op' : MonTerm → MonTerm → MonTerm

data OpenMonTerm (n : ℕ) : Set where
  v  : Fin n → OpenMonTerm n 
  e' : OpenMonTerm n
  op' : OpenMonTerm n → OpenMonTerm n → OpenMonTerm n 

liftMonExpr : MonTerm -> Staged MonTerm zero
liftMonExpr e' = liftConstant e'
liftMonExpr (op' x y) =
  liftBinary (op') (liftMonExpr x) (liftMonExpr y)

liftOpenMonExpr : {n : ℕ} → OpenMonTerm n -> Staged (OpenMonTerm n) zero
liftOpenMonExpr (v fin) = laterConst (code (v fin)) 
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


