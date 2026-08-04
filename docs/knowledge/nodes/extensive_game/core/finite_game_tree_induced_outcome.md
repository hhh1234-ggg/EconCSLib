---
id: game_theory.extensive_game.core.finite_game_tree_induced_outcome
title: Finite Game-Tree Strategy Induces An Outcome
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.core.game_tree
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
  declarations:
    - GameTree.Strategy
    - GameTree.outcome
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - game-tree
  - strategy
  - outcome
---

# Finite Game-Tree Strategy Induces An Outcome

For a finite perfect-information, no-chance `GameTree`, a strategy selects one
child at every decision node. Recursively following those selections reaches a
leaf and therefore determines its payoff vector.

Finiteness and nonempty children are structural properties of `GameTree`, so
this specialization needs no separate termination certificate. It is narrower
than the general Arena claim in
[[game_theory.extensive_game.core.strategy_profile_induced_outcome]], where
cycles and non-player-controlled transitions are permitted.

## References

- [MFoGT, Section 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. In a finite perfect-information tree without Nature, a strategy profile selects a unique terminal path.
