# Super-V: A Framework for Verified Distributed Applications

Super-V is a framework for implementing replicated-state applications and using automated SMT-based verification to determine their correctness.

To get started, take a look at an example application: the one-shot election algorithm defined in `lib/SuperV/Example/Election.hs`. To verify this application, first install the Cabal build tool for Haskell and the CVC5 SMT solver. Then run the following commands:

```
(super-v) $ cabal repl
ghci> SuperV.Example.Election.checkAllVCs
...
```

This process verifies a key safety property for the election algorithm: that two nodes cannot come to accept two different elected leaders.

## An eDSL with Decidable Verification

Super-V provides an embedded DSL for the implementation of executable update handlers and the definition of verification specifications. Functions written in this DSL are automatically translated into SMT representations that fall within the Extended EPR fragment of logic. Staying within this fragment ensures that the underlying SMT solver can reliably discharge the necessary verification conditions.

## Case Study: Log Consensus

See `lib/SuperV/Example/LogConsensus.hs` for a more involved example: a full log-consensus algorithm with the same safety guarantees and fault-tolerance as the Raft algorithm.
