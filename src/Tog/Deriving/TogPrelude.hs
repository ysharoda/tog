module Tog.Deriving.TogPrelude (prelude) where

prelude :: [String] 
prelude =
   prod ++ nat ++
   fin ++ pred' ++ vec ++ unit ++ empty ++
   subst ++ sym ++ cong ++
   isZero ++ zeroNotSuc ++ 
   trans ++ lemma ++ sucInj ++ lookup' ++
   codeModule ++ stagingModule

prod :: [String]
prod =
 ("record Prod (A B : Set): Set where {" ++
   "constructor prodC ;" ++
   "field { " ++ 
     "fst : A ; " ++
     "snd : B } }") : [] 

nat :: [String]
nat =
 ("data Nat : Set where { " ++ 
    "zero : Nat ;" ++ 
    "suc  : Nat -> Nat }") : []

fin :: [String] 
fin =
 ("data Fin (n : Nat) : Set where { " ++
    "fzero : {m : Nat} (p : n == suc m) -> Fin n ;" ++
    "fsuc  : {m : Nat} (p : n == suc m) (i : Fin m) -> Fin n }")  : []   

pred' :: [String]
pred' =
  "pred : Nat -> Nat " :
  "pred zero = zero  "  :
  "pred (suc n) = n "  : []

vec :: [String]
vec =
 ("data Vec (A : Set) (n : Nat) : Set where { " ++ 
    "nil  : n == zero -> Vec A n ; " ++ 
    "cons : {m : Nat} (p : n == suc m) (x : A) (xs : Vec A m) -> Vec A n }") : [] 

unit :: [String]
unit = 
 ("data Unit : Set where { " ++ 
    "unit : Unit } ") : [] 

empty :: [String]
empty =
  "EmptyT : Set " :
  "EmptyT = (A : Set) -> A " : []

subst :: [String] 
subst =
  "subst : {A : Set} {x y : A} (P : A -> Set) -> x == y -> P x -> P y " :
  "subst P = J (\\ x y _ -> P x -> P y) (\\ x p -> p) " : [] 

sym :: [String]
sym = 
  "sym : {A : Set} {x : A} {y : A} -> x == y -> y == x " : 
  "sym {A} {x} {y} p = subst (\\  y -> y == x) p refl " : []

cong :: [String]
cong =
  "cong : {A B : Set} {x : A} {y : A} (f : A -> B) -> x == y -> f x == f y " : 
  "cong f p = subst (\\  y -> f _ == f y) p refl "                            : []

isZero :: [String]
isZero =
  "IsZero : Nat -> Set " : 
  "IsZero zero = Unit  " : 
  "IsZero (suc n) = EmptyT " : []

zeroNotSuc :: [String]
zeroNotSuc =
  "zeroNOTsuc : {n : Nat} -> zero == suc n -> EmptyT " : 
  "zeroNOTsuc p = subst IsZero p unit " : []

trans :: [String]
trans =
  "trans : {A : Set} {x : A} {y : A} {z : A} -> x == y -> y == z -> x == z " : 
  "trans {A} {x} p q = subst (\\  y -> x == y) q p " : []

lemma :: [String]
lemma =
  "lemma : {n m : Nat} -> n == suc m -> n == zero -> EmptyT " : 
  "lemma p q = zeroNOTsuc (trans (sym q) p) " : []

sucInj :: [String]
sucInj =
  "sucInj : {n m : Nat} -> suc n == suc m -> n == m " :
  "sucInj p = cong pred p " : [] 

lookup' :: [String]
lookup' =
  "lookup : {A : Set} (n : Nat) (i : Fin n) (v : Vec A n) -> A " : 
  "lookup {A} n (fzero {m} p) (nil q) = lemma p q A " : 
  "lookup {A} n (fzero {m} p) (cons {l} q x xs)  = x "           : 
  "lookup {A} n (fsuc {m} p i) (nil q) = lemma p q A " : 
  "lookup {A} n (fsuc {m} p i) (cons {l} q x xs) = lookup m i (subst (Vec A) (sucInj (trans (sym q) p)) xs) "    : []

-- Code Module  

wrap :: [String]
wrap =
  ("data Wrap (A : Set) : Set where {" ++
     "Q : A -> Wrap A }") : [] 

stage :: [String]
stage =
  ("data Stage : Set where { " ++
     "s0 : Stage ; " ++
     "s1 : Stage } ") : [] 

codeRep :: [String]
codeRep = 
  "CodeRep : (A : Set) (s : Stage) -> Set" :
  "CodeRep A s0 = A" :
  "CodeRep A s1 = Wrap (CodeRep A s0)" : []

uncode :: [String]
uncode =
  "uncode : {A : Set} -> CodeRep A s1 -> CodeRep A s0" :
  "uncode (Q x) = x" : []

code :: [String]
code =
  "code : {A : Set} -> CodeRep A s0 -> CodeRep A s1" : 
  "code x = Q x" : []
  
run :: [String]
run =
  "run : {A : Set} -> CodeRep A s1 -> A" : 
  "run (Q x) = x" : []

codeModule :: [String]
codeModule =
  wrap ++ stage ++ codeRep ++
  uncode ++ code ++ run 
  
-- Staging Module

choice :: [String]
choice =
  ("data Choice : Set where { " ++
     "Expr : Choice ; " ++
     "Const : Choice }") : []

comp :: [String]
comp =
  ("data Comp (A : Set) (s : Stage) : Set where { " ++
    "Computation : Choice -> CodeRep A s -> Comp A s }") : []

staged :: [String]
staged =
  ("data Staged (A : Set) : Set where { " ++ 
    "Now : A -> Staged A ; " ++ 
    "Later : Comp A s1 -> Staged A } ") : [] 

expr :: [String]
expr = 
 "expr : {A : Set} -> CodeRep A s1 -> Staged A" : 
 "expr x = Later (Computation Expr x)" : [] 

const' :: [String]
const' = 
 "const : {A : Set} -> CodeRep A s1 -> Staged A" : 
 "const x = Later (Computation Const x)" : [] 

stage0 :: [String]
stage0 = 
 "stage0 : {A : Set} -> A -> Staged A" : 
 "stage0 x = Now x" : []

stage1 :: [String]
stage1 = 
 "stage1 : {A B : Set} -> (A -> B) -> (CodeRep A s1 -> CodeRep B s1) -> Staged A -> Staged B" : 
 "stage1 f g (Now x) = Now (f x)" : 
 "stage1 f g (Later (Computation _ x)) = expr (g x)" : []

stage2 :: [String]
stage2 = 
 "stage2 : {A B C : Set} -> (A -> B -> C) -> (CodeRep A s1 -> CodeRep B s1 -> CodeRep C s1) -> Staged A -> Staged B -> Staged C " : 
 "stage2 f _ (Now x) (Now y) = stage0 (f x y)" : 
 "stage2 _ g (Now x) (Later (Computation _ y)) = expr (g (code x) y)" : 
 "stage2 _ g (Later (Computation _ x)) (Now y) = expr (g x (code y))" : 
 "stage2 _ g (Later (Computation _ x)) (Later (Computation _ y)) = expr (g x y)" : []

codeLift1 :: [String]
codeLift1 =
  "codeLift1 : {A B : Set} -> (A -> B) -> (CodeRep A s1 -> CodeRep B s1)" : 
 "codeLift1 f x = code (f (uncode x))" : []

codeLift2 :: [String]
codeLift2 = 
 "codeLift2 : {A B C : Set} -> (A -> B -> C) -> (CodeRep A s1 -> CodeRep B s1 -> CodeRep C s1)" : 
 "codeLift2 f x y = code (f (uncode x) (uncode y))" : []

stagingModule :: [String]
stagingModule =
  choice ++ comp ++ staged ++
  expr ++ const' ++
  stage0 ++ stage1 ++ stage2 ++ codeLift1 ++ codeLift2  

