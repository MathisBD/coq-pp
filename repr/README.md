# Description

# Code structure

- Class.v : the main `Repr` typeclass.
- Deriving.v : a command to derive `Repr` instances automatically for inductives, implemented using MetaCoq.
- LocallyNameless.v : a small locally nameless API to help build MetaCoq terms.
- Instances.v : standard `Repr` instances. Most are automatically derived.
- Utils.v : various Coq and MetaCoq utility functions.