---
id: game_theory.extensive_game.core.nature_player
title: Nature In Extensive Games
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
  - nature
  - chance
---

# Nature In Extensive Games

An extensive game with Nature has chance nodes at which no strategic player
chooses an action. Instead, the game description specifies a probability
distribution over successors. A strategy profile of the strategic players then
induces a probability distribution over terminal outcomes.

## Lean Status

Not yet formalized by the structural EFG core. The current
`ControlledGame.isNonPlayerState` predicate (and compatibility name
`isChanceState`) records only a non-player-controlled nonterminal state; it
does not supply a probability mass function, stochastic kernel, or law on
successors. That distinct structural concept is recorded in
[[game_theory.extensive_game.core.non_player_controlled_state]].

## References

- [MFoGT, Section 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nature or hazard player chooses successors according to specified probability distributions.
