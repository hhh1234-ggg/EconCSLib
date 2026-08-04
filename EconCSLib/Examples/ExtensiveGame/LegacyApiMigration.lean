/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.History

/-!
# Legacy payoff-aware API migration

This regression checks that the historical state-payoff API is a thin adapter
over the canonical payoff-free structural owners. It deliberately covers only
the compatibility surface introduced by the minimal-core migration.
-/

namespace Examples.ExtensiveGame.LegacyApiMigration

universe uN uU

variable {N : Type uN} {U : Type uU}

#check _root_.ExtensiveGame.ofArena
#check _root_.ExtensiveGame.ofControlledGame

/-- Forgetting structural data and reattaching the existing payoff is a
round-trip. -/
example (G : _root_.ExtensiveGame N U) :
    _root_.ExtensiveGame.ofControlledGame
      G.toControlledGame G.payoff = G :=
  _root_.ExtensiveGame.ofControlledGame_toControlledGame_self G

/-- Historical root reachability is the canonical controlled-game
reachability predicate. -/
example (G : _root_.ExtensiveGame N U) (state : G.State) :
    G.IsReachable state ↔
      G.toControlledGame.IsReachable state :=
  _root_.ExtensiveGame.isReachable_iff_toControlledGame G state

/-- The payoff-aware history unfolding forgets exactly to the canonical
controlled-game unfolding. -/
example (G : _root_.ExtensiveGame N U) :
    G.unfold.toControlledGame =
      G.toControlledGame.unfold :=
  _root_.ExtensiveGame.unfold_toControlledGame G

/-- Forgetting one layer further yields the canonical Arena history
unfolding. -/
example (G : _root_.ExtensiveGame N U) :
    G.unfold.toArena =
      G.toArena.unfoldFrom G.init :=
  _root_.ExtensiveGame.unfold_toArena G

end Examples.ExtensiveGame.LegacyApiMigration
