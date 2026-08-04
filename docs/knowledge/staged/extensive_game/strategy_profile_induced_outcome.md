---
id: game_theory.extensive_game.core.strategy_profile_induced_outcome
title: Strategy Profile And Induced Outcome
kind: definition
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - strategy
  - outcome
---

# Strategy Profile And Induced Outcome

A strategy profile $\sigma=(\sigma_i)_{i\in I}$ specifies one successor at every
decision position. Starting from the origin and following the successor prescribed
by the player who controls the current position gives a unique terminal outcome
$$
  F(\sigma)\in R.
$$
Payoffs under the strategy profile are then $g_i(F(\sigma))$.

This conclusion requires more structure than an arbitrary Arena profile:

- a resolver for every non-player-controlled transition, or a no-chance
  certificate;
- a deterministic execution construction from the profile;
- a termination certificate before a terminal history can be extracted; and
- an objective or payoff interpretation on that terminal history.

With a chance law, a strategic profile generally induces a distribution on
plays or outcomes rather than one deterministic outcome. For Arenas with
cycles, a complete play may never terminate.

## Lean Status

The general profile-to-terminal-outcome chain above is not yet formalized.
`Arena.CompletePlayFromHistory` provides the legal finite-or-infinite path
carrier but intentionally supplies no profile resolver or termination theorem.
The finite, perfect-information, no-chance `GameTree` specialization does have
a formalized deterministic outcome; see
[[game_theory.extensive_game.core.finite_game_tree_induced_outcome]].

## References

- [MFoGT, Section 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A strategy profile induces a unique terminal outcome.
