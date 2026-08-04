/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.Basic
import EconCSLib.GameTheory.ExtensiveGame.Structural.Reachability
import EconCSLib.GameTheory.ExtensiveGame.Structural.History
import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed

/-!
# Structural core facade

The narrow canonical pre-stability import for the payoff-free structural
semantics of extensive games. It exposes only the Arena dynamics, controlled
dynamics, finite reachability, typed histories, measure-free complete plays,
the payoff-free controlled information/strategy carrier, and optional
represented-information well-formedness certificates.

Structural termination, bounded execution, PMF or measurable execution,
objectives, winning predicates, lawful-subgame and recall certificates,
payoff-aware compatibility types, relations, equilibrium, simulation, and
compilers are deliberately outside this facade.

In particular, this facade does not transitively import the payoff-aware
`ExtensiveGame` structure from `ExtensiveGame.Basic`.

Broader interfaces can add finite/recall/subgame certificates, bounded
execution, objectives, probability, and solution concepts without changing
this structural layer.
-/
