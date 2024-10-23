# Description

A Coq pretty printing library.

# Setup 

Setup a local opam switch with coq :

```
opam switch create . 5.2.0 --repos default,coq-released=https://coq.inria.fr/opam/released
```

and select yes (Y) when asked to create as a new package.

Use dune build to build the only Coq examples, and dune install if you want to step through the Coq files interactively.