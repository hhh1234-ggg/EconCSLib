/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.Strategy

Strategies for extensive-form games built on the Arena framework.

## Main definitions

* `Strategy G i` — a strategy for player `i`: choose an action at each
  nonterminal state they control
* `StrategyProfile G` — strategies for all players
* `completeProfile` — fill in a strategy profile with an action-selection function
-/

namespace ExtensiveGame

variable {N : Type*} {U : Type*}

/-- A strategy for player `i`: at each nonterminal state where `i` is the
mover, specify which action to take.

The nonterminal premise is essential because terminal mover labels are
semantically ignored by `ControlledGame`. In particular, a terminal state
labelled `some i` does not create an impossible strategy coordinate. -/
def Strategy (G : ExtensiveGame N U) (i : N) :=
  (s : G.State) → G.mover s = some i →
    ¬ G.isTerminal s → G.Action s

/-- A strategy profile: a strategy for each player. -/
def StrategyProfile (G : ExtensiveGame N U) :=
  (i : N) → G.Strategy i

/-- Given a strategy profile, extract the action at a nonterminal
player-controlled state. Returns `none` when the state is non-player-controlled.

Terminal states cannot be queried: their mover labels are semantically
irrelevant and their action fibers are empty. -/
def StrategyProfile.actionAt {G : ExtensiveGame N U}
    (σ : StrategyProfile G) (s : G.State)
    (hnonterminal : ¬ G.isTerminal s) :
    Option (Σ _ : N, G.Action s) :=
  match h : G.mover s with
  | some i => some ⟨i, σ i s h hnonterminal⟩
  | none => none

end ExtensiveGame
