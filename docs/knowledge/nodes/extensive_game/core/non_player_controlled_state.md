---
id: game_theory.extensive_game.core.non_player_controlled_state
title: Non-Player-Controlled Nonterminal State
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Structural.Basic
  declarations:
    - ControlledGame.isNonPlayerState
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - control
  - non-player
---

# Non-Player-Controlled Nonterminal State

A non-player-controlled state is a nonterminal state whose mover label is
`none`. This is purely structural: it says that no strategic player controls
the transition, but does not specify how the next action or successor is
selected.

A probabilistic Nature/chance interpretation requires additional stochastic
data and is tracked separately in
[[game_theory.extensive_game.core.nature_player]].

## References

- [MFoGT, Section 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nature nodes motivate distinguishing strategic control from non-player transitions; probability is additional data.
