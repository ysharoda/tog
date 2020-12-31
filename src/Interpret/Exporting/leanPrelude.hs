module Interpret.Exporting.LeanPrelude where

import Text.PrettyPrint.Leijen

leanPrelude :: Doc 
leanPrelude =
  header <$$> prod <$$> wrap <$$> stage <$$> stageOrder <$$>
  codeRep <$$> uncode <$$> code <$$> run <$$> choice <$$>
  comp <$$> staged <$$> expr' <$$> const' <$$>
  stage0 <$$> stage1 <$$> stage2 <$$>
  codeLift1 <$$> codeLift2 <$$>
  footer 

header :: Doc 
header = text $ "section Prelude" 

createDef :: String -> [String] -> String -> Doc
createDef def constrs op = text def <$$> (indent 2 $ vsep $ map text constrs) <$$> text op

-- Product Type
prod :: Doc
prod = createDef "structure Prod (a b  : Type) : Type := "  ["(fst : a)","(snd : b)"]  "" 

-- Staging
wrap :: Doc
wrap = createDef "inductive Wrap (A : Type) : Type" ["| Q : A → Wrap"] "open Wrap" 


stage :: Doc
stage = 
  createDef "inductive Stage : Type" ["| s0 : Stage","| s1 : Stage"] "open Stage" 

stageOrder :: Doc
stageOrder =
  createDef "def stageOrder : Stage → ℕ" ["| s0 := 0", "| s1 := 1"] ""  

codeRep :: Doc
codeRep =
  createDef "def CodeRep (A : Type) : Stage → Type"
     ["| s0 := A", "| s1 := have stageOrder s0 < stageOrder s1, from dec_trivial, Wrap (CodeRep s0)"]
     "using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf stageOrder⟩]}"

uncode :: Doc
uncode =
  createDef "def uncode {A : Type} : CodeRep A s1 → CodeRep A s0" ["| (Q x) := x"] "" 

code :: Doc
code = 
  createDef "def code {A : Type} : CodeRep A s0 → CodeRep A s1" ["| x := Q x"] ""   

run :: Doc
run = createDef "def run {A : Type} : CodeRep A s1 → A" ["| (Q x) := x"] ""   

choice :: Doc
choice = createDef "inductive Choice : Type" ["| Expr : Choice","| Const : Choice"]  "open Choice" 

comp :: Doc
comp = createDef "inductive Comp (A : Type) (s : Stage) : Type"
         ["| Computation : Choice → CodeRep A s → Comp"]  
         "open Comp" 

staged :: Doc
staged = createDef "inductive Staged (A : Type) : Type"
          ["| Now : A → Staged","| Later : Comp A s1 → Staged"] 
          "open Staged" 

expr' :: Doc
expr' = createDef "def expr' {A : Type} : CodeRep A s1 → Staged A := "
                   ["λ x, Later (Computation Expr x)"] ""

const' :: Doc
const' = createDef "def const {A : Type} : CodeRep A s1 → Staged A := "
                   ["λ x, Later (Computation Const x)"] ""

stage0 :: Doc
stage0 = createDef "def stage0 {A : Type} : A → Staged A := "
                   ["λ x, Now x"] ""

stage1 :: Doc
stage1 =
  createDef "def stage1 {A B : Type} : (A → B) → (CodeRep A s1 → CodeRep B s1) → (Staged A → Staged B)"
            ["| f g (Now x) := Now (f x)","| f g (Later (Computation _ x)) := expr' (g x)"] "" 

stage2 :: Doc
stage2 =
  createDef "def stage2 {A B C : Type} : (A → B → C) → (CodeRep A s1 → CodeRep B s1 → CodeRep C s1) → (Staged A → Staged B → Staged C)"
      ["| f _ (Now x) (Now y) := stage0 (f x y)",
       "| _ g (Now x) (Later (Computation _ y)) := expr' (g (code x) y)",
       "| _ g (Later (Computation _ x)) (Now y) := expr' (g x (code y))", 
       "| _ g (Later (Computation _ x)) (Later (Computation _ y)) := expr' (g x y)"] ""

codeLift1 :: Doc
codeLift1 =
  createDef "def codeLift1 {A B : Type} : (A → B) → (CodeRep A s1 → CodeRep B s1) := "
           ["λ f x, code (f (uncode x)) "] ""

codeLift2 :: Doc
codeLift2 =
  createDef "def codeLift2 {A B C : Type} : (A → B → C) → (CodeRep A s1 → CodeRep B s1 → CodeRep C s1) := "
            ["λ f x y, code (f (uncode x) (uncode y))"] ""

footer :: Doc
footer = text "end Prelude" 
