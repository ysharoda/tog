module Monoid where 

record Monoid (A : Set) : Set where
  constructor monoid
  field
    e  : A
    op : A -> A -> A
    lunit : {x : A} -> (op e x) == x
    runit : {x : A} -> (op x e) == x
    assoc : {x y z : A} -> (op x (op y z)) == (op (op x y) z)


