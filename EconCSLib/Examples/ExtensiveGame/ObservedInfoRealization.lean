/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed

/-!
# Decision-information realization regressions

The raw observed-game carrier intentionally permits abstract information
coordinates. This file demonstrates why standard EFG models must state
`AllDecisionInfoRepresented`, then checks that the complete-information
presentation supplies the certificate.
-/

namespace EconCSLib.Examples.ExtensiveGame.ObservedInfoRealization

/-- A one-state, one-action looping decision problem. -/
def loopingBase : ControlledGame Unit where
  State := Unit
  Action := fun _ => Unit
  next := fun _ _ => ()
  init := ()
  mover := fun _ => some ()

/-- Add one unrealized information value (`true`) with no abstract action.

All concrete decision histories map to `false`, whose action type is `Unit`,
so the local `actionEquiv` law remains satisfied. -/
def withJunkInfo :
    _root_.ExtensiveGame.ControlledObservedGame Unit where
  base := loopingBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Bool
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ _ => false
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := fun _ information =>
    if information then PEmpty else Unit
  actionEquiv := fun _ _ _ _ => Equiv.refl Unit

/-- The unrealized empty-action coordinate empties the raw strategy carrier.
This is the intended negative regression: the wide carrier alone makes no
standard-EFG well-formedness claim. -/
theorem no_pureStrategy_with_junk :
    ¬ Nonempty (withJunkInfo.PureStrategy ()) := by
  rintro ⟨strategy⟩
  exact PEmpty.elim (strategy true)

/-- The negative example cannot satisfy the explicit no-junk certificate. -/
theorem junk_not_allDecisionInfoRepresented :
    ¬ withJunkInfo.AllDecisionInfoRepresented := by
  intro hrepresented
  rcases hrepresented () true with ⟨witness⟩
  have hfalse : false = true := witness.infoAt_eq
  cases hfalse

/-- The canonical complete-information adapter has exactly the represented
decision histories as its information carrier. -/
theorem completeInformation_has_no_junk :
    (_root_.ExtensiveGame.ControlledObservedGame.completeInformation
      loopingBase).AllDecisionInfoRepresented :=
  _root_.ExtensiveGame.ControlledObservedGame.completeInformation_allDecisionInfoRepresented
    loopingBase

/-- The realization certificate is sufficient to recover an inhabited raw
pure-profile carrier, with no terminal-mover normalization assumption. -/
theorem completeInformation_has_pureProfile :
    Nonempty
      (_root_.ExtensiveGame.ControlledObservedGame.completeInformation
        loopingBase).PureProfile :=
  completeInformation_has_no_junk.nonempty_pureProfile

end EconCSLib.Examples.ExtensiveGame.ObservedInfoRealization
