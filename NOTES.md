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