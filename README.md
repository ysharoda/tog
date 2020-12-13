Deriving Library Definitions from Theory Expressions

This projects aim to eliminate the boilerplate associated with building libraries of Algebra in formal systems. Instead of library builders providing every definition of the library, they write theory expressions and an interpreter generates the described theories and many of their constructions. 

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
  - `-o` determines the output mode, which can be one of
     -- `tog`: The output is displayed in tog's syntax. 
     -- `agda`: The output is displayed in Agda's syntax. 
     -- `agd-pred-style`: The output is displayed in Agda's syntax. The theories presentations are in predicate style, as in its Agda's standard library. 
  

## References
[1]



