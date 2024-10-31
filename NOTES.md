# TODO

- Profile and optimize the pretty-printing computation.
- Improve naming of the derived Repr instance (repr_t is always there).

# Workshop Paper ?

# Solving Evars

- either in tmUnquote/tmUnquoteTyped : call Typing.solve_evars
- create a new constructor in the template monad tmSolveEvars : term -> TemplateMonad term

# Declaring universe polymorphic definitions

change tmMkDefinition to take in a definition_entry instead of a raw term (similar to tmMkInductive which takes in a mutual_inductive_entry). Maybe even use constant_entry so we also handle parameters at the same time ?

# Strings 

bytestrings (MetaCoq.Utils) vs ascii strings (Coq stdlib).
Ideally I use bytestrings (both in pprint and in repr), but I don't want pprint to force users to use MetaCoq.Utils.

Solutions ?
- extract bytestrings to a separate library ?
- eventually deprecate ascii strings in Coq stdlib ?

# MetaCoq bugs

1. Quoting primitive strings does not work : 
```
MetaCoq Test Quote "hello"%pstring.
(* (String.String "hello"%pstring) *) 
```

2. noccurn_between is incorrect (the base case contains && instead of ||).

