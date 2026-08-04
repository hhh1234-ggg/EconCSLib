/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore

/-!
# Structural-core positive import boundary

The narrow structural facade exposes the game carriers, occurrence-sensitive
history/play types, root presentations, and pure strategies.
-/

#check Arena
#check ControlledGame
#check ControlledGame.isNonPlayerState
#check ControlledGame.isChanceState
#check Arena.Reachable
#check ControlledGame.IsReachable
#check Arena.History
#check Arena.unfoldEndpoint
#check Arena.CompletePlayFromHistory
#check ExtensiveGame.ControlledObservedGame
#check ExtensiveGame.ControlledObservedGame.ContinuationRootPresentation
#check ExtensiveGame.ControlledObservedGame.PureStrategy
#check ExtensiveGame.ControlledObservedGame.PureProfile
#check ExtensiveGame.ControlledObservedGame.AllDecisionInfoRepresented
#check ExtensiveGame.ControlledObservedGame.relabelPlayers
#check ExtensiveGame.ControlledObservedGame.relabelPureProfileEquiv

namespace ExtensiveGame.StructuralCoreImportBoundary

universe uN uA uS uO uI uP

/-- The controlled-observed carrier preserves independent action and state
universes. In particular, its base action fiber lives with `InfoAction` in
`uA`, while its base state remains in `uS`. -/
example {N : Type uN}
    (G : ControlledObservedGame.{uN, uA, uS, uO, uI, uP} N) :
    ControlledGame.{uN, uA, uS} N :=
  G.base

end ExtensiveGame.StructuralCoreImportBoundary

/- These guarded failures prevent the structural facade from accidentally
regaining the payoff-aware compatibility carrier through a transitive import. -/

/-- error: Unknown identifier `ExtensiveGame` -/
#guard_msgs in
#check ExtensiveGame

/-- error: Unknown identifier `ExtensiveGame.payoff` -/
#guard_msgs in
#check ExtensiveGame.payoff
