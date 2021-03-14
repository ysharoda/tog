# Deriving Library Definitions from Theory Expressions

This project aims to eliminate the boilerplate associated with building libraries of Algebra in formal systems. Instead of library builders providing every definition of the library, they write theory expressions and an interpreter generates the described theories and many of their constructions. 

## Installation
```
  git clone https://github.com/ysharoda/Deriving-Definitions.git
  cd Deriving-Definitions
  make install 
```

## Running
```
  tog [options] [file] 
```
`tog --help` gives the full options. Of specific interest are the following options:
  - `-m` to choose the operating mode.
    - `i` or `interpret`: calls the interpreter on theory expressions. When calling the interpreter, a target language needs to be chosen, see `-t` option
    - `tc` or `typecheck`: calls the type checker on an input tog file.
    - `f` or `flatten`: to flatten theory expressions without going through generation and exporting phases. 
  - `-l` to choose the target language of the interpreter, which can be one of
    - `tog`: The output is printed in tog's syntax. This is the default output mode. 
    - `agda`: The output is printed in Agda's syntax. 
    - `agd-pred-style`: The output is printed in Agda's syntax. The theory presentations are in predicate style, as in Agda's standard library.
    - `lean`: The output is printed in Lean's syntax.  
  - `-f` to determine the destination folder. This folder is used with the `agda`, `agda-pred-style`, and `lean` in which every theory with its related constructions is a module. In the case of `tog`, all theories are part of the same module, because tog lacks proper import. The value passed to `-f` is the name of the file containing the modules. The default destination folder is `./output-generated`. 
  
## Input Syntax
The Syntax of the expressions is adapted from [1].
```
  Map m = {a0 to b0 ; a1 to b1 ; ... ; an to bn}
  Theory T = {a0 : t0 ; a1 : t1, ... ; an : tn}
  T' = extend T {a0 : t0 ; a1 : t1 ; ... ; an : tn}
  T' = rename T m 
  T' = combine T1 m1 T2 m2 over T
  I  = id from T1 to T2
```

## The Interpreter
To generate a library from the expressions above, we extend [tog](https://github.com/bitonic/tog) by creating a 3-phase interpreter that works as follows:
  - A *flattener* creates a theory graph from the theory expressions, based on their semantics as described in [1].
  - A *generator* that leverages the information contained in theory presentations. The constructions generated are typically provided by library builders.
  - An *exporter* that translates this code from tog into feature-rich languages. 

## References
[1] Carette, J., O'Connor, R. and Sharoda, Y., 2019. Building on the Diamonds between Theories: Theory Presentation Combinators. arXiv preprint arXiv:1812.08079.

[2] Carette, J., Farmer, W.M. and Sharoda, Y., 2020, July. Leveraging the information contained in theory presentations. In International Conference on Intelligent Computer Mathematics (pp. 55-70). Springer, Cham.



