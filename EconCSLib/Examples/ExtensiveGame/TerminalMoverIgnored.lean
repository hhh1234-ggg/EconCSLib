/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.BehaviorStrategy
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Terminal mover labels do not create strategy coordinates

Regression test for the payoff-free observed-game carrier. A terminal state
may retain an unnormalized player mover label in `ControlledGame`, but it must
not create an impossible pure-strategy obligation.
-/

namespace EconCSLib.Examples.ExtensiveGame.TerminalMoverIgnored

/-- A one-state terminal controlled game whose ignored mover label is
`some ()`. -/
def terminalBase : ControlledGame Unit where
  State := Unit
  Action := fun _ => PEmpty
  next := fun _ action => nomatch action
  init := ()
  mover := fun _ => some ()

/-- The complete-information presentation of `terminalBase`. -/
def observed : _root_.ExtensiveGame.ControlledObservedGame Unit :=
  _root_.ExtensiveGame.ControlledObservedGame.completeInformation terminalBase

/-- There are no decision-information states, despite the terminal mover
label. -/
theorem infoState_isEmpty : IsEmpty (observed.InfoState ()) := by
  constructor
  intro information
  exact information.2.2 ⟨fun action => nomatch action⟩

/-- Consequently, a pure strategy exists without selecting an action at the
terminal state. -/
def pureStrategy : observed.PureStrategy () :=
  fun information => (infoState_isEmpty.false information).elim

/-- The corresponding one-player profile exists as well. -/
def pureProfile : observed.PureProfile :=
  fun _ => pureStrategy

/-- The same dynamics with the historical state-payoff wrapper. -/
def legacyGame : _root_.ExtensiveGame Unit Unit :=
  _root_.ExtensiveGame.ofControlledGame terminalBase (fun _ _ => ())

instance legacyActionFintype :
    (state : legacyGame.State) → Fintype (legacyGame.Action state) :=
  fun _state => by
    change Fintype PEmpty
    infer_instance

/-- The historical pure-strategy carrier also ignores the terminal mover
label: its nonterminal premise is contradictory at the only state. -/
def legacyPureStrategy : legacyGame.Strategy () :=
  fun _state _hmover hnonterminal =>
    (hnonterminal ⟨fun action => nomatch action⟩).elim

/-- The historical behavior-strategy carrier has the same decision-state
contract and therefore needs no simplex over the empty terminal action type. -/
def legacyBehaviorStrategy : legacyGame.BehaviorStrategy () :=
  fun _state _hmover hnonterminal =>
    (hnonterminal ⟨fun action => nomatch action⟩).elim

/-- The action-query API requires a nonterminal proof, so it cannot inspect
the ignored terminal mover coordinate. -/
example (profile : legacyGame.StrategyProfile) :
    (s : legacyGame.State) →
      ¬ legacyGame.isTerminal s →
        Option (Σ _ : Unit, legacyGame.Action s) :=
  fun state hnonterminal => profile.actionAt state hnonterminal

end EconCSLib.Examples.ExtensiveGame.TerminalMoverIgnored
