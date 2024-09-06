# An eDSL with Decidable Verification

To test it out on your system, first install the Cabal build tool for
Haskell and the CVC5 SMT solver.

```
$ cabal update
$ cabal repl
ghci> Ddsl.Example.Election.verifyElection mempty
VC #1. Proven (...s)
VC #2. Proven (...s)
VC #3. Proven (...s)
VC #4. Proven (...s)
VC #5. Proven (...s)
VC #6. Proven (...s)
VC #7. Proven (...s)
```
