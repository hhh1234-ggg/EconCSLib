/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.History

/-!
# Merged endpoints retain distinct histories

This regression witnesses that the Arena state model does not identify two
typed histories merely because they end at the same world state.
-/

namespace Examples.HistoryDiamond

/-- A root with two distinct actions that lead to the same terminal state. -/
inductive State
  | root
  | terminal

/-- The diamond Arena has two histories to one endpoint. -/
def arena : Arena where
  State := State
  Action
    | .root => Bool
    | .terminal => PEmpty
  next
    | .root, _ => .terminal

/-- The history taking the first root action. -/
def left : arena.History State.root State.terminal :=
  Arena.History.nil.snoc false

/-- The history taking the second root action. -/
def right : arena.History State.root State.terminal :=
  Arena.History.nil.snoc true

/-- Distinct actions remain distinct histories even though their endpoint is
the same world state. -/
theorem left_ne_right : left ≠ right := by
  intro h
  cases h

/-- Either diamond branch witnesses the same endpoint reachability
proposition. -/
theorem root_reachable_terminal :
    arena.Reachable State.root State.terminal :=
  left.toReachable

/-- Proof irrelevance identifies the two reachability proofs even though the
histories that produced them remain distinct. -/
theorem left_right_reachability_proofs_eq :
    left.toReachable = right.toReachable :=
  Subsingleton.elim _ _

/-- The public bridge records existence without collapsing occurrence
histories. -/
theorem reachable_and_distinct_occurrences :
    arena.Reachable State.root State.terminal ∧
      left ≠ right := by
  exact
    ⟨(arena.reachable_iff_nonempty_history
      State.root State.terminal).mpr ⟨left⟩,
      left_ne_right⟩

end Examples.HistoryDiamond
