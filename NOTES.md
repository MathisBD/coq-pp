# Template monad improvements

The implementation of tmMkDefinition and friends is a bit buggy ; for instance :
1. handling of universes and evars in tmMkDefinition and friends is inconsistent and a bit bugged
2. the API is non-uniform : e.g. for inductives we can pass in a mutual_inductive_entry, but for definitions and axioms we can only pass in a term. 
3. related operations have separate implementations (e.g. TmDefinition vs TmDefinitionTerm, or TmAxiom vs TmAxiomTerm). Some are ad-hoc and some go through Plugin_core. This makes it harder to maintain.

In the long run, it could be a good idea to reimplement this cleanly : have all core "tmMk" operations use an _entry_, and implement derived operations (e.g. make a definition with only the body) on top of these.

# TODO

- Profile and optimize the pretty-printing computation.
- Improve naming of the derived Repr instance (repr_t is always there) --> check what Derive NoConfusion does.
- Check what Derive NoConfusion does for mutual inductives (generate only one function or all functions ?)

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

