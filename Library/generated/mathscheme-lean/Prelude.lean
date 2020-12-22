section Prelude
structure Prod (a b  : Type) : Type := 
  (fst : a)
  (snd : b)

inductive Wrap (A : Type) : Type
  | Q : A → Wrap
open Wrap
inductive Stage : Type
  | s0 : Stage
  | s1 : Stage
open Stage
def stageOrder : Stage → ℕ
  | s0 := 0
  | s1 := 1

def CodeRep (A : Type) : Stage → Type
  | s0 := A
  | s1 := have stageOrder s0 < stageOrder s1, from dec_trivial, Wrap (CodeRep s0)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf stageOrder⟩]}
def uncode {A : Type} : CodeRep A s1 → CodeRep A s0
  | (Q x) := x

def code {A : Type} : CodeRep A s0 → CodeRep A s1
  | x := Q x

def run {A : Type} : CodeRep A s1 → A
  | (Q x) := x

inductive Choice : Type
  | Expr : Choice
  | Const : Choice
open Choice
inductive Comp (A : Type) (s : Stage) : Type
  | Computation : Choice → CodeRep A s → Comp
open Comp
inductive Staged (A : Type) : Type
  | Now : A → Staged
  | Later : Comp A s1 → Staged
open Staged
def expr' {A : Type} : CodeRep A s1 → Staged A := 
  λ x, Later (Computation Expr x)

def const {A : Type} : CodeRep A s1 → Staged A := 
  λ x, Later (Computation Const x)

def stage0 {A : Type} : A → Staged A := 
  λ x, Now x

def stage1 {A B : Type} : (A → B) → (CodeRep A s1 → CodeRep B s1) → (Staged A → Staged B)
  | f g (Now x) := Now (f x)
  | f g (Later (Computation _ x)) := expr' (g x)

def stage2 {A B C : Type} : (A → B → C) → (CodeRep A s1 → CodeRep B s1 → CodeRep C s1) → (Staged A → Staged B → Staged C)
  | f _ (Now x) (Now y) := stage0 (f x y)
  | _ g (Now x) (Later (Computation _ y)) := expr' (g (code x) y)
  | _ g (Later (Computation _ x)) (Now y) := expr' (g x (code y))
  | _ g (Later (Computation _ x)) (Later (Computation _ y)) := expr' (g x y)

def codeLift1 {A B : Type} : (A → B) → (CodeRep A s1 → CodeRep B s1) := 
  λ f x, code (f (uncode x)) 

def codeLift2 {A B C : Type} : (A → B → C) → (CodeRep A s1 → CodeRep B s1 → CodeRep C s1) := 
  λ f x y, code (f (uncode x) (uncode y))

end Prelude