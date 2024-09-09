# An eDSL with Decidable Verification

To test it out on your system, first install the Cabal build tool for
Haskell and the CVC5 SMT solver.

```
$ git clone https://github.com/cuplv/ddsl
$ cd ddsl
$ cabal update
$ cabal repl
ghci> Ddsl.Example.Election.verifyElection
...
```
