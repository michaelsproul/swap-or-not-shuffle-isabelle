# Swap-or-Not Shuffle (Isabelle/HOL)

This is a formalisation of the swap-or-not shuffling algorithm
as used in Ethereum 2.0.

## Outline

* `AbstractSwapOrNotShuffle.thy`: definition of swap-or-not shuffle in terms of
  Abelian groups. We prove that under some mild assumptions about the input
  list, swap-or-not shuffle yields a permutation.

## TODO

The next step will be to instantiate the abstract shuffle with the key and round functions
used in Eth2, which are based on hashing and modulo arithmetic on integers.

Once that is complete, I hope to prove equivalence between the optimised
implementation of the algorithm that we use in Lighthouse, and the
one-at-a-time shuffling defined by the Ethereum 2 specification.

## More Info

* [Swap-or-not shuffle](https://link.springer.com/content/pdf/10.1007%2F978-3-642-32009-5_1.pdf)
* [Ethereum 2's instantiation](https://github.com/ethereum/eth2.0-specs/blob/v0.8.3/specs/core/0_beacon-chain.md#compute_shuffled_index)
* [Lighthouse optimised implementation](https://github.com/sigp/lighthouse/tree/master/eth2/utils/swap_or_not_shuffle)
