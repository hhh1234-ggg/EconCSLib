/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# General payoff-free controlled well-formedness

Optional represented-information certificates for `ControlledObservedGame`.
They are deliberately separate from the carrier:
applications that allow abstract or as-yet-unrealized information coordinates
can use the raw data, while standard EFG models can state explicitly that every
strategy coordinate is a real decision coordinate.

No certificate in this module adds finiteness, payoff, probability, recall, or
termination.

## Main definitions

* `ControlledObservedGame.DecisionInfoWitness`
* `ControlledObservedGame.AllDecisionInfoRepresented`
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-- A concrete nonterminal player decision representing an abstract
information state. -/
structure DecisionInfoWitness
    (G : ControlledObservedGame N) (i : N)
    (information : G.InfoState i) where
  /-- Representing complete history. -/
  history : G.base.History
  /-- Player `i` controls the endpoint. -/
  mover : G.base.mover history.1 = some i
  /-- The endpoint is a genuine decision rather than a terminal mover label. -/
  nonterminal : ¬ G.base.isTerminal history.1
  /-- The history represents the requested information state. -/
  infoAt_eq : G.infoAt history i mover nonterminal = information

/-- Every declared decision-information state is represented by a concrete
nonterminal player decision.

This is the explicit no-junk-coordinate assumption for the general carrier. -/
def AllDecisionInfoRepresented
    (G : ControlledObservedGame N) : Prop :=
  ∀ (i : N) (information : G.InfoState i),
    Nonempty (G.DecisionInfoWitness i information)

namespace AllDecisionInfoRepresented

/-- Every represented information coordinate has a legal abstract action. -/
theorem nonempty_infoAction
    (hrepresented : G.AllDecisionInfoRepresented)
    (i : N) (information : G.InfoState i) :
    Nonempty (G.InfoAction i information) := by
  rcases hrepresented i information with ⟨witness⟩
  have haction :
      Nonempty (G.base.Action witness.history.1) :=
    not_isEmpty_iff.mp witness.nonterminal
  have habstract :=
    haction.map
      (G.actionEquiv witness.history i witness.mover
        witness.nonterminal).symm
  simpa [witness.infoAt_eq] using habstract

/-- Represented information makes each raw pure-strategy carrier
inhabited. -/
theorem nonempty_pureStrategy
    (hrepresented : G.AllDecisionInfoRepresented)
    (i : N) :
    Nonempty (G.PureStrategy i) := by
  classical
  exact
    ⟨fun information =>
      Classical.choice
        (hrepresented.nonempty_infoAction
          i information)⟩

/-- Represented information makes the raw pure-profile carrier
inhabited. -/
theorem nonempty_pureProfile
    (hrepresented : G.AllDecisionInfoRepresented) :
    Nonempty G.PureProfile := by
  classical
  exact
    ⟨fun i =>
      Classical.choice
        (hrepresented.nonempty_pureStrategy i)⟩

end AllDecisionInfoRepresented

/-- Complete-information presentations have no junk decision-information
coordinates. -/
theorem completeInformation_allDecisionInfoRepresented
    (base : ControlledGame N) :
    (completeInformation base).AllDecisionInfoRepresented := by
  intro i information
  exact
    ⟨{ history := information.1
       mover := information.2.1
       nonterminal := information.2.2
       infoAt_eq := rfl }⟩

end ExtensiveGame.ControlledObservedGame
