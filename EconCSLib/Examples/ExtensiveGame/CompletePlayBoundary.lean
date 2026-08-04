/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay

/-!
# Concrete complete-play boundary regressions

One finite Arena reaches a terminal history in one step and then stutters
forever. A second cyclic Arena has a genuinely infinite complete play.
-/

namespace EconCSLib.Examples.ExtensiveGame.CompletePlayBoundary

namespace Finite

inductive State
  | root
  | terminal

/-- A one-step Arena ending at a terminal state. -/
def arena : Arena where
  State := State
  Action
    | .root => Unit
    | .terminal => PEmpty
  next
    | .root, _ => .terminal

/-- The unique one-action terminal history. -/
def terminalHistory : arena.HistoryFrom State.root :=
  ⟨State.terminal, Arena.History.nil.snoc ()⟩

theorem terminal_isTerminal :
    arena.IsTerminal State.terminal :=
  ⟨fun action => nomatch action⟩

theorem terminalHistory_isChild :
    arena.IsChildFrom terminalHistory
      (Arena.HistoryFrom.nil arena State.root) :=
  Arena.IsChildFrom.snoc
    (Arena.HistoryFrom.nil arena State.root) ()

/-- A finite complete play: take the only action, then use the canonical
terminal stutter. -/
def play : arena.CompletePlayFrom State.root :=
  Arena.CompletePlayFromHistory.prependChild
    terminalHistory_isChild
    (Arena.CompletePlayFromHistory.stutter
      terminalHistory terminal_isTerminal)

@[simp]
theorem play_at_one :
    play.historyAt 1 = terminalHistory :=
  rfl

/-- Once coordinate one is terminal, every later coordinate is the identical
complete history. -/
theorem play_stutters_forever (offset : ℕ) :
    play.historyAt (1 + offset) = terminalHistory := by
  rw [play.at_add_eq_of_terminal 1 (by simpa using terminal_isTerminal)]
  exact play_at_one

theorem play_eventuallyTerminates :
    play.EventuallyTerminates :=
  ⟨1, by simpa using terminal_isTerminal⟩

end Finite

namespace Infinite

/-- A one-state cyclic Arena with one available action forever. -/
def arena : Arena where
  State := Unit
  Action := fun _ => Unit
  next := fun _ _ => ()

/-- The complete history after exactly `n` loop occurrences. -/
def historyAt : ℕ → arena.HistoryFrom ()
  | 0 => Arena.HistoryFrom.nil arena ()
  | n + 1 =>
      ⟨(), (historyAt n).2.snoc ()⟩

/-- The cyclic Arena's canonical concrete infinite play. -/
def play : arena.CompletePlayFrom () where
  historyAt := historyAt
  historyAt_zero := rfl
  step := fun _n => Or.inr ⟨(), rfl⟩

/-- Every coordinate remains nonterminal, so the play is genuinely infinite. -/
theorem play_neverTerminates :
    play.NeverTerminates := by
  intro n hterminal
  exact hterminal.false ()

end Infinite

end EconCSLib.Examples.ExtensiveGame.CompletePlayBoundary
